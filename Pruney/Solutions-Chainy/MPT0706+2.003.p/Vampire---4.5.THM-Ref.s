%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   21 (  69 expanded)
%              Number of leaves         :    3 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 ( 381 expanded)
%              Number of equality atoms :   24 ( 126 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,plain,(
    $false ),
    inference(global_subsumption,[],[f15,f20])).

fof(f20,plain,(
    sK0 = sK1 ),
    inference(forward_demodulation,[],[f19,f17])).

fof(f17,plain,(
    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f10,f11,f13,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f13,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK0 != sK1
    & r1_tarski(sK1,k2_relat_1(sK2))
    & r1_tarski(sK0,k2_relat_1(sK2))
    & k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & r1_tarski(X1,k2_relat_1(X2))
        & r1_tarski(X0,k2_relat_1(X2))
        & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( sK0 != sK1
      & r1_tarski(sK1,k2_relat_1(sK2))
      & r1_tarski(sK0,k2_relat_1(sK2))
      & k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r1_tarski(X1,k2_relat_1(X2))
      & r1_tarski(X0,k2_relat_1(X2))
      & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X1,k2_relat_1(X2))
            & r1_tarski(X0,k2_relat_1(X2))
            & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X1,k2_relat_1(X2))
          & r1_tarski(X0,k2_relat_1(X2))
          & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_funct_1)).

fof(f11,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    inference(forward_demodulation,[],[f18,f12])).

fof(f12,plain,(
    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,(
    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f10,f11,f14,f16])).

fof(f14,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f15,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (29661)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.45  % (29652)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.45  % (29661)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(global_subsumption,[],[f15,f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    sK0 = sK1),
% 0.20/0.46    inference(forward_demodulation,[],[f19,f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f10,f11,f13,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f6])).
% 0.20/0.46  fof(f6,plain,(
% 0.20/0.46    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    sK0 != sK1 & r1_tarski(sK1,k2_relat_1(sK2)) & r1_tarski(sK0,k2_relat_1(sK2)) & k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (X0 != X1 & r1_tarski(X1,k2_relat_1(X2)) & r1_tarski(X0,k2_relat_1(X2)) & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (sK0 != sK1 & r1_tarski(sK1,k2_relat_1(sK2)) & r1_tarski(sK0,k2_relat_1(sK2)) & k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f5,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (X0 != X1 & r1_tarski(X1,k2_relat_1(X2)) & r1_tarski(X0,k2_relat_1(X2)) & k10_relat_1(X2,X0) = k10_relat_1(X2,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.46    inference(flattening,[],[f4])).
% 0.20/0.46  fof(f4,plain,(
% 0.20/0.46    ? [X0,X1,X2] : ((X0 != X1 & (r1_tarski(X1,k2_relat_1(X2)) & r1_tarski(X0,k2_relat_1(X2)) & k10_relat_1(X2,X0) = k10_relat_1(X2,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X1,k2_relat_1(X2)) & r1_tarski(X0,k2_relat_1(X2)) & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)) => X0 = X1))),
% 0.20/0.46    inference(negated_conjecture,[],[f2])).
% 0.20/0.46  fof(f2,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X1,k2_relat_1(X2)) & r1_tarski(X0,k2_relat_1(X2)) & k10_relat_1(X2,X0) = k10_relat_1(X2,X1)) => X0 = X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t161_funct_1)).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    v1_funct_1(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    v1_relat_1(sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 0.20/0.46    inference(forward_demodulation,[],[f18,f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    k10_relat_1(sK2,sK0) = k10_relat_1(sK2,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f10,f11,f14,f16])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    r1_tarski(sK1,k2_relat_1(sK2))),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    sK0 != sK1),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (29661)------------------------------
% 0.20/0.46  % (29661)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (29661)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (29661)Memory used [KB]: 10490
% 0.20/0.46  % (29661)Time elapsed: 0.064 s
% 0.20/0.46  % (29661)------------------------------
% 0.20/0.46  % (29661)------------------------------
% 0.20/0.46  % (29649)Success in time 0.107 s
%------------------------------------------------------------------------------
