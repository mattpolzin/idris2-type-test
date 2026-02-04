module TTImp.Raw

import Core.WithData
import Core.TT

import TTImp.TTImp
import TTImp.Elab
import TTImp.Elab.Check
import TTImp.Unelab

import Libraries.Data.WithData

mutual
  iFnOptToRaw : FnOpt' KindedName -> FnOpt' Name
  iFnOptToRaw Unsafe = Unsafe
  iFnOptToRaw Inline = Inline
  iFnOptToRaw NoInline = NoInline
  iFnOptToRaw Deprecate = Deprecate
  iFnOptToRaw TCInline = TCInline
  iFnOptToRaw (Hint x) = Hint x
  iFnOptToRaw (GlobalHint x) = GlobalHint x
  iFnOptToRaw ExternFn = ExternFn
  iFnOptToRaw (ForeignFn ts) = ForeignFn $ iRawToRawImp <$> ts
  iFnOptToRaw (ForeignExport ts) = ForeignExport $ iRawToRawImp <$> ts
  iFnOptToRaw Invertible = Invertible
  iFnOptToRaw (Totality treq) = Totality treq
  iFnOptToRaw Macro = Macro
  iFnOptToRaw (SpecArgs ns) = SpecArgs ns

  iImpClauseToRaw : ImpClause' KindedName -> ImpClause' Name
  iImpClauseToRaw (PatClause fc lhs rhs) = PatClause fc (iRawToRawImp lhs) (iRawToRawImp rhs)
  iImpClauseToRaw (WithClause fc lhs rig wval prf flags cls) = (WithClause fc (iRawToRawImp lhs) rig (iRawToRawImp wval) prf flags (iImpClauseToRaw <$> cls))
  iImpClauseToRaw (ImpossibleClause fc lhs) = ImpossibleClause fc (iRawToRawImp lhs)

  iImpDataToRaw : ImpData' KindedName -> ImpData' Name
  iImpDataToRaw (MkImpData fc n tycon opts datacons) = MkImpData fc n (iRawToRawImp <$> tycon) opts (map iRawToRawImp <$> datacons)
  iImpDataToRaw (MkImpLater fc n tycon) = MkImpLater fc n (iRawToRawImp tycon)

  iClaimDataToRaw : IClaimData KindedName -> IClaimData Name
  iClaimDataToRaw (MkIClaimData rig vis opts type) = MkIClaimData rig vis (iFnOptToRaw <$> opts) (iRawToRawImp <$> type)

  iImpRecordDataToRaw : ImpRecordData KindedName -> ImpRecordData Name
  iImpRecordDataToRaw (MkImpRecord header body) = MkImpRecord (map (map (map iRawToRawImp)) <$> header) (map (map (map iRawToRawImp)) <$> body)

  iImpDeclToRaw : ImpDecl' KindedName-> ImpDecl' Name
  iImpDeclToRaw (IClaim x) = IClaim (iClaimDataToRaw <$> x)
  iImpDeclToRaw (IData fc x mtreq dat) = IData fc x mtreq (iImpDataToRaw dat)
  iImpDeclToRaw (IDef fc n cls) = IDef fc n (iImpClauseToRaw <$> cls)
  iImpDeclToRaw (IParameters fc xs decls) = IParameters fc (map (map iRawToRawImp) <$> xs) (iImpDeclToRaw <$> decls)
  iImpDeclToRaw (IRecord fc mstr x mtreq y) = IRecord fc mstr x mtreq (iImpRecordDataToRaw <$> y)
  iImpDeclToRaw (IFail fc mstr decls) = IFail fc mstr (iImpDeclToRaw <$> decls)
  iImpDeclToRaw (INamespace fc mi decls) = INamespace fc mi (iImpDeclToRaw <$> decls)
  iImpDeclToRaw (ITransform fc n t u) = ITransform fc n (iRawToRawImp t) (iRawToRawImp u)
  iImpDeclToRaw (IRunElabDecl fc t) = IRunElabDecl fc (iRawToRawImp t)
  iImpDeclToRaw (IPragma fc ns f) = IPragma fc ns f
  iImpDeclToRaw (ILog x) = ILog x
  iImpDeclToRaw (IBuiltin fc x n) = IBuiltin fc x n

  iFieldUpdateToRaw : IFieldUpdate' KindedName -> IFieldUpdate' Name
  iFieldUpdateToRaw (ISetField path t) = ISetField path (iRawToRawImp t)
  iFieldUpdateToRaw (ISetFieldApp path t) = ISetFieldApp path (iRawToRawImp t)

  iAltTypeToRaw : AltType' KindedName -> AltType' Name
  iAltTypeToRaw FirstSuccess = FirstSuccess
  iAltTypeToRaw Unique = Unique
  iAltTypeToRaw (UniqueDefault t) = UniqueDefault (iRawToRawImp t)

  export
  iRawToRawImp : IRawImp -> RawImp
  iRawToRawImp (IVar fc x) = IVar fc $ fullName x
  iRawToRawImp (IPi fc rig pinfo mn argTy retTy) = (IPi fc rig ((map iRawToRawImp) pinfo) mn (iRawToRawImp argTy) (iRawToRawImp retTy))
  iRawToRawImp (ILam fc rig pinfo mn argTy lamTy) = (ILam fc rig ((map iRawToRawImp) pinfo) mn (iRawToRawImp argTy) (iRawToRawImp lamTy))
  iRawToRawImp (ILet fc lhsFC rig n nTy nVal scope) = (ILet fc lhsFC rig n (iRawToRawImp nTy) (iRawToRawImp nVal) (iRawToRawImp scope))
  iRawToRawImp (ICase fc fopts t ty cls) = (ICase fc (iFnOptToRaw <$> fopts) (iRawToRawImp t) (iRawToRawImp ty) (iImpClauseToRaw <$> cls))
  iRawToRawImp (ILocal fc decls t) = (ILocal fc (iImpDeclToRaw <$> decls) (iRawToRawImp t))
  iRawToRawImp (ICaseLocal fc uname internalName args t) = (ICaseLocal fc uname internalName args (iRawToRawImp t))
  iRawToRawImp (IUpdate fc upds t) = (IUpdate fc (iFieldUpdateToRaw <$> upds) (iRawToRawImp t))
  iRawToRawImp (IApp fc t u) = (IApp fc (iRawToRawImp t) (iRawToRawImp u))
  iRawToRawImp (IAutoApp fc t u) = (IAutoApp fc (iRawToRawImp t) (iRawToRawImp u))
  iRawToRawImp (INamedApp fc t n u) = (INamedApp fc (iRawToRawImp t) n (iRawToRawImp u))
  iRawToRawImp (IWithApp fc t u) = (IWithApp fc (iRawToRawImp t) (iRawToRawImp u))
  iRawToRawImp (ISearch fc depth) = (ISearch fc depth)
  iRawToRawImp (IAlternative fc alt ts) = (IAlternative fc (iAltTypeToRaw alt) (iRawToRawImp <$> ts))
  iRawToRawImp (IRewrite fc t u) = (IRewrite fc (iRawToRawImp t) (iRawToRawImp u))
  iRawToRawImp (ICoerced fc t) = (ICoerced fc (iRawToRawImp t))
  iRawToRawImp (IBindHere fc bm t) = (IBindHere fc bm (iRawToRawImp t))
  iRawToRawImp (IBindVar fc n) = (IBindVar fc n)
  iRawToRawImp (IAs fc nameFC side n t) = (IAs fc nameFC side n (iRawToRawImp t))
  iRawToRawImp (IMustUnify fc x t) = (IMustUnify fc x (iRawToRawImp t))
  iRawToRawImp (IDelayed fc lz t) = (IDelayed fc lz (iRawToRawImp t))
  iRawToRawImp (IDelay fc t) = (IDelay fc (iRawToRawImp t))
  iRawToRawImp (IForce fc t) = (IForce fc (iRawToRawImp t))
  iRawToRawImp (IQuote fc t) = (IQuote fc (iRawToRawImp t))
  iRawToRawImp (IQuoteName fc n) = (IQuoteName fc n)
  iRawToRawImp (IQuoteDecl fc decls) = (IQuoteDecl fc (iImpDeclToRaw <$> decls))
  iRawToRawImp (IUnquote fc t) = (IUnquote fc (iRawToRawImp t))
  iRawToRawImp (IRunElab fc requireExtension t) = (IRunElab fc requireExtension (iRawToRawImp t))
  iRawToRawImp (IPrimVal fc c) = (IPrimVal fc c)
  iRawToRawImp (IType fc) = (IType fc)
  iRawToRawImp (IHole fc str) = (IHole fc str)
  iRawToRawImp (IUnifyLog fc x t) = (IUnifyLog fc x (iRawToRawImp t))
  iRawToRawImp (Implicit fc bindIfUnsolved) = (Implicit fc bindIfUnsolved)
  iRawToRawImp (IWithUnambigNames fc xs t) = (IWithUnambigNames fc xs (iRawToRawImp t))

