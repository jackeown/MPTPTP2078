%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:39 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 219 expanded)
%              Number of leaves         :   18 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  119 ( 304 expanded)
%              Number of equality atoms :   38 ( 165 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10336)Termination reason: Refutation not found, incomplete strategy

% (10336)Memory used [KB]: 10746
% (10336)Time elapsed: 0.140 s
fof(f451,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f173,f443,f450])).

fof(f450,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f444])).

fof(f444,plain,
    ( $false
    | spl3_2 ),
    inference(resolution,[],[f421,f172])).

fof(f172,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f170])).

% (10336)------------------------------
% (10336)------------------------------
% (10332)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (10315)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% (10323)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f170,plain,
    ( spl3_2
  <=> r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f421,plain,(
    ! [X28,X27] : r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(X27,X27,X27,X27,X27,X27,X27,X28))),k10_relat_1(sK2,X28)) ),
    inference(superposition,[],[f96,f185])).

fof(f185,plain,(
    ! [X2,X3] : k2_xboole_0(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X3) = X3 ),
    inference(resolution,[],[f139,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f139,plain,(
    ! [X4,X3] : r1_tarski(k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3)),X3) ),
    inference(superposition,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f30,f49,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f42,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f29,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f49])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f96,plain,(
    ! [X12,X13] : r1_tarski(k10_relat_1(sK2,X12),k10_relat_1(sK2,k2_xboole_0(X12,X13))) ),
    inference(superposition,[],[f58,f89])).

fof(f89,plain,(
    ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    inference(resolution,[],[f38,f27])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f39,f55])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f443,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f437])).

fof(f437,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f301,f168])).

fof(f168,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_1
  <=> r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f301,plain,(
    ! [X26,X27] : r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(X26,X26,X26,X26,X26,X26,X26,X27))),k10_relat_1(sK2,X26)) ),
    inference(superposition,[],[f96,f71])).

fof(f71,plain,(
    ! [X2,X3] : k2_xboole_0(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X2) = X2 ),
    inference(resolution,[],[f52,f33])).

fof(f173,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f164,f170,f166])).

fof(f164,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK1))
    | ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f51,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f50])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f51,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))) ),
    inference(definition_unfolding,[],[f28,f50,f50])).

fof(f28,plain,(
    ~ r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:04:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.48  % (10309)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (10307)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (10308)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (10334)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (10317)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (10310)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (10311)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (10317)Refutation not found, incomplete strategy% (10317)------------------------------
% 0.20/0.52  % (10317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (10317)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (10317)Memory used [KB]: 10746
% 0.20/0.52  % (10317)Time elapsed: 0.114 s
% 0.20/0.52  % (10317)------------------------------
% 0.20/0.52  % (10317)------------------------------
% 0.20/0.52  % (10312)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (10321)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (10313)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (10329)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (10336)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (10328)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (10330)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (10337)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (10319)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (10324)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (10322)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (10314)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (10327)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (10335)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (10318)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (10331)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (10316)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (10320)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (10333)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (10325)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.46/0.55  % (10336)Refutation not found, incomplete strategy% (10336)------------------------------
% 1.46/0.55  % (10336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (10313)Refutation found. Thanks to Tanya!
% 1.46/0.55  % SZS status Theorem for theBenchmark
% 1.46/0.55  % SZS output start Proof for theBenchmark
% 1.46/0.55  % (10336)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (10336)Memory used [KB]: 10746
% 1.46/0.55  % (10336)Time elapsed: 0.140 s
% 1.46/0.55  fof(f451,plain,(
% 1.46/0.55    $false),
% 1.46/0.55    inference(avatar_sat_refutation,[],[f173,f443,f450])).
% 1.46/0.55  fof(f450,plain,(
% 1.46/0.55    spl3_2),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f444])).
% 1.46/0.55  fof(f444,plain,(
% 1.46/0.55    $false | spl3_2),
% 1.46/0.55    inference(resolution,[],[f421,f172])).
% 1.46/0.55  fof(f172,plain,(
% 1.46/0.55    ~r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK1)) | spl3_2),
% 1.46/0.55    inference(avatar_component_clause,[],[f170])).
% 1.46/0.55  % (10336)------------------------------
% 1.46/0.55  % (10336)------------------------------
% 1.46/0.56  % (10332)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.46/0.56  % (10315)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.46/0.56  % (10323)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.46/0.57  fof(f170,plain,(
% 1.46/0.57    spl3_2 <=> r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK1))),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.46/0.57  fof(f421,plain,(
% 1.46/0.57    ( ! [X28,X27] : (r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(X27,X27,X27,X27,X27,X27,X27,X28))),k10_relat_1(sK2,X28))) )),
% 1.46/0.57    inference(superposition,[],[f96,f185])).
% 1.46/0.57  fof(f185,plain,(
% 1.46/0.57    ( ! [X2,X3] : (k2_xboole_0(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X3) = X3) )),
% 1.46/0.57    inference(resolution,[],[f139,f33])).
% 1.46/0.57  fof(f33,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.46/0.57    inference(cnf_transformation,[],[f18])).
% 1.46/0.57  fof(f18,plain,(
% 1.46/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.46/0.57    inference(ennf_transformation,[],[f3])).
% 1.46/0.57  fof(f3,axiom,(
% 1.46/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.46/0.57  fof(f139,plain,(
% 1.46/0.57    ( ! [X4,X3] : (r1_tarski(k1_setfam_1(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3)),X3)) )),
% 1.46/0.57    inference(superposition,[],[f52,f53])).
% 1.46/0.57  fof(f53,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 1.46/0.57    inference(definition_unfolding,[],[f30,f49,f49])).
% 1.46/0.57  fof(f49,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.46/0.57    inference(definition_unfolding,[],[f31,f48])).
% 1.46/0.57  fof(f48,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.46/0.57    inference(definition_unfolding,[],[f37,f47])).
% 1.46/0.57  fof(f47,plain,(
% 1.46/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.46/0.57    inference(definition_unfolding,[],[f41,f46])).
% 1.46/0.57  fof(f46,plain,(
% 1.46/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.46/0.57    inference(definition_unfolding,[],[f42,f45])).
% 1.46/0.57  fof(f45,plain,(
% 1.46/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.46/0.57    inference(definition_unfolding,[],[f43,f44])).
% 1.46/0.57  fof(f44,plain,(
% 1.46/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f12])).
% 1.46/0.57  fof(f12,axiom,(
% 1.46/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.46/0.57  fof(f43,plain,(
% 1.46/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f11])).
% 1.46/0.57  fof(f11,axiom,(
% 1.46/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.46/0.57  fof(f42,plain,(
% 1.46/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f10])).
% 1.46/0.57  fof(f10,axiom,(
% 1.46/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.46/0.57  fof(f41,plain,(
% 1.46/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f9])).
% 1.46/0.57  fof(f9,axiom,(
% 1.46/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.46/0.57  fof(f37,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f8])).
% 1.46/0.57  fof(f8,axiom,(
% 1.46/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.46/0.57  fof(f31,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f7])).
% 1.46/0.57  fof(f7,axiom,(
% 1.46/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.46/0.57  fof(f30,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f6])).
% 1.46/0.57  fof(f6,axiom,(
% 1.46/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.46/0.57  fof(f52,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X0)) )),
% 1.46/0.57    inference(definition_unfolding,[],[f29,f50])).
% 1.46/0.57  fof(f50,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.46/0.57    inference(definition_unfolding,[],[f32,f49])).
% 1.46/0.57  fof(f32,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.46/0.57    inference(cnf_transformation,[],[f13])).
% 1.46/0.57  fof(f13,axiom,(
% 1.46/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.46/0.57  fof(f29,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f4])).
% 1.46/0.57  fof(f4,axiom,(
% 1.46/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.46/0.57  fof(f96,plain,(
% 1.46/0.57    ( ! [X12,X13] : (r1_tarski(k10_relat_1(sK2,X12),k10_relat_1(sK2,k2_xboole_0(X12,X13)))) )),
% 1.46/0.57    inference(superposition,[],[f58,f89])).
% 1.46/0.57  fof(f89,plain,(
% 1.46/0.57    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) )),
% 1.46/0.57    inference(resolution,[],[f38,f27])).
% 1.46/0.57  fof(f27,plain,(
% 1.46/0.57    v1_relat_1(sK2)),
% 1.46/0.57    inference(cnf_transformation,[],[f24])).
% 1.46/0.57  fof(f24,plain,(
% 1.46/0.57    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) & v1_relat_1(sK2)),
% 1.46/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f23])).
% 1.46/0.57  fof(f23,plain,(
% 1.46/0.57    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))) & v1_relat_1(sK2))),
% 1.46/0.57    introduced(choice_axiom,[])).
% 1.46/0.57  fof(f17,plain,(
% 1.46/0.57    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) & v1_relat_1(X2))),
% 1.46/0.57    inference(ennf_transformation,[],[f16])).
% 1.46/0.57  fof(f16,negated_conjecture,(
% 1.46/0.57    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 1.46/0.57    inference(negated_conjecture,[],[f15])).
% 1.46/0.57  fof(f15,conjecture,(
% 1.46/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k10_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).
% 1.46/0.57  fof(f38,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 1.46/0.57    inference(cnf_transformation,[],[f19])).
% 1.46/0.57  fof(f19,plain,(
% 1.46/0.57    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.46/0.57    inference(ennf_transformation,[],[f14])).
% 1.46/0.57  fof(f14,axiom,(
% 1.46/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).
% 1.46/0.57  fof(f58,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.46/0.57    inference(resolution,[],[f39,f55])).
% 1.46/0.57  fof(f55,plain,(
% 1.46/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.46/0.57    inference(equality_resolution,[],[f35])).
% 1.46/0.57  fof(f35,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.46/0.57    inference(cnf_transformation,[],[f26])).
% 1.46/0.57  fof(f26,plain,(
% 1.46/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.57    inference(flattening,[],[f25])).
% 1.46/0.57  fof(f25,plain,(
% 1.46/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.46/0.57    inference(nnf_transformation,[],[f1])).
% 1.46/0.57  fof(f1,axiom,(
% 1.46/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.46/0.57  fof(f39,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f20])).
% 1.46/0.57  fof(f20,plain,(
% 1.46/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.46/0.57    inference(ennf_transformation,[],[f2])).
% 1.46/0.57  fof(f2,axiom,(
% 1.46/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.46/0.57  fof(f443,plain,(
% 1.46/0.57    spl3_1),
% 1.46/0.57    inference(avatar_contradiction_clause,[],[f437])).
% 1.46/0.57  fof(f437,plain,(
% 1.46/0.57    $false | spl3_1),
% 1.46/0.57    inference(resolution,[],[f301,f168])).
% 1.46/0.57  fof(f168,plain,(
% 1.46/0.57    ~r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0)) | spl3_1),
% 1.46/0.57    inference(avatar_component_clause,[],[f166])).
% 1.46/0.57  fof(f166,plain,(
% 1.46/0.57    spl3_1 <=> r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0))),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.46/0.57  fof(f301,plain,(
% 1.46/0.57    ( ! [X26,X27] : (r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(X26,X26,X26,X26,X26,X26,X26,X27))),k10_relat_1(sK2,X26))) )),
% 1.46/0.57    inference(superposition,[],[f96,f71])).
% 1.46/0.57  fof(f71,plain,(
% 1.46/0.57    ( ! [X2,X3] : (k2_xboole_0(k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X2) = X2) )),
% 1.46/0.57    inference(resolution,[],[f52,f33])).
% 1.46/0.57  fof(f173,plain,(
% 1.46/0.57    ~spl3_1 | ~spl3_2),
% 1.46/0.57    inference(avatar_split_clause,[],[f164,f170,f166])).
% 1.46/0.57  fof(f164,plain,(
% 1.46/0.57    ~r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK1)) | ~r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k10_relat_1(sK2,sK0))),
% 1.46/0.57    inference(resolution,[],[f51,f54])).
% 1.46/0.57  fof(f54,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.46/0.57    inference(definition_unfolding,[],[f40,f50])).
% 1.46/0.57  fof(f40,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f22])).
% 1.46/0.57  fof(f22,plain,(
% 1.46/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.46/0.57    inference(flattening,[],[f21])).
% 1.46/0.57  fof(f21,plain,(
% 1.46/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.46/0.57    inference(ennf_transformation,[],[f5])).
% 1.46/0.57  fof(f5,axiom,(
% 1.46/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.46/0.57  fof(f51,plain,(
% 1.46/0.57    ~r1_tarski(k10_relat_1(sK2,k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k1_setfam_1(k6_enumset1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))))),
% 1.46/0.57    inference(definition_unfolding,[],[f28,f50,f50])).
% 1.46/0.57  fof(f28,plain,(
% 1.46/0.57    ~r1_tarski(k10_relat_1(sK2,k3_xboole_0(sK0,sK1)),k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)))),
% 1.46/0.57    inference(cnf_transformation,[],[f24])).
% 1.46/0.57  % SZS output end Proof for theBenchmark
% 1.46/0.57  % (10313)------------------------------
% 1.46/0.57  % (10313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (10313)Termination reason: Refutation
% 1.46/0.57  
% 1.46/0.57  % (10313)Memory used [KB]: 11257
% 1.46/0.57  % (10313)Time elapsed: 0.130 s
% 1.46/0.57  % (10313)------------------------------
% 1.46/0.57  % (10313)------------------------------
% 1.58/0.57  % (10305)Success in time 0.208 s
%------------------------------------------------------------------------------
