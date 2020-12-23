%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:00 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 191 expanded)
%              Number of leaves         :   13 (  58 expanded)
%              Depth                    :   16
%              Number of atoms          :  149 ( 366 expanded)
%              Number of equality atoms :   22 ( 100 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f587,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f582,f586])).

fof(f586,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f585])).

fof(f585,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f584,f24])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

fof(f584,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_2 ),
    inference(resolution,[],[f95,f98])).

fof(f98,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k9_relat_1(X3,k1_setfam_1(k1_enumset1(X4,X4,X5))),k9_relat_1(X3,X4))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f42,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_setfam_1(k1_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1))))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f35,f38,f38])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

fof(f95,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_2
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f582,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f571])).

fof(f571,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f507,f91])).

fof(f91,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_1
  <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f507,plain,(
    ! [X2,X3] : r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(sK2,X3)))),X3) ),
    inference(subsumption_resolution,[],[f488,f24])).

fof(f488,plain,(
    ! [X2,X3] :
      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(sK2,X3)))),X3)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f426,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))),k9_relat_1(X0,X2))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f42,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k1_setfam_1(k1_enumset1(X1,X1,X0)))
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f43,f41])).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f28,f29,f29])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f426,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X4,k9_relat_1(sK2,k10_relat_1(sK2,X3)))
      | r1_tarski(X4,X3) ) ),
    inference(superposition,[],[f43,f423])).

fof(f423,plain,(
    ! [X0] : k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k10_relat_1(sK2,X0)))) ),
    inference(subsumption_resolution,[],[f422,f24])).

fof(f422,plain,(
    ! [X0] :
      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k10_relat_1(sK2,X0))))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f127,f25])).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f127,plain,(
    ! [X8,X9] :
      ( ~ v1_funct_1(X8)
      | k9_relat_1(X8,k10_relat_1(X8,X9)) = k1_setfam_1(k1_enumset1(X9,X9,k9_relat_1(X8,k10_relat_1(X8,X9))))
      | ~ v1_relat_1(X8) ) ),
    inference(forward_demodulation,[],[f118,f41])).

fof(f118,plain,(
    ! [X8,X9] :
      ( k9_relat_1(X8,k10_relat_1(X8,X9)) = k1_setfam_1(k1_enumset1(k9_relat_1(X8,k10_relat_1(X8,X9)),k9_relat_1(X8,k10_relat_1(X8,X9)),X9))
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8) ) ),
    inference(resolution,[],[f113,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(subsumption_resolution,[],[f110,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f110,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f48,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1 ) ),
    inference(resolution,[],[f34,f40])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f38])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f96,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f87,f93,f89])).

fof(f87,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))
    | ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) ),
    inference(resolution,[],[f86,f44])).

fof(f86,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))) ),
    inference(forward_demodulation,[],[f39,f41])).

fof(f39,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f26,f38,f38])).

fof(f26,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:16:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (24669)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (24670)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.53  % (24671)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (24680)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (24688)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (24667)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (24685)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.54  % (24668)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (24675)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (24666)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (24693)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (24674)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (24689)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (24673)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (24695)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (24684)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (24672)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (24691)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (24687)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (24677)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (24690)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.50/0.56  % (24682)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.50/0.56  % (24676)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.50/0.56  % (24681)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.50/0.56  % (24692)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.50/0.56  % (24679)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.50/0.56  % (24676)Refutation not found, incomplete strategy% (24676)------------------------------
% 1.50/0.56  % (24676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (24676)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (24676)Memory used [KB]: 10618
% 1.50/0.56  % (24676)Time elapsed: 0.126 s
% 1.50/0.56  % (24676)------------------------------
% 1.50/0.56  % (24676)------------------------------
% 1.50/0.56  % (24683)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.50/0.56  % (24686)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.50/0.56  % (24678)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.67/0.58  % (24682)Refutation not found, incomplete strategy% (24682)------------------------------
% 1.67/0.58  % (24682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (24682)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.58  
% 1.67/0.58  % (24682)Memory used [KB]: 10618
% 1.67/0.58  % (24682)Time elapsed: 0.168 s
% 1.67/0.58  % (24682)------------------------------
% 1.67/0.58  % (24682)------------------------------
% 1.67/0.58  % (24694)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.67/0.58  % (24672)Refutation found. Thanks to Tanya!
% 1.67/0.58  % SZS status Theorem for theBenchmark
% 1.67/0.58  % SZS output start Proof for theBenchmark
% 1.67/0.58  fof(f587,plain,(
% 1.67/0.58    $false),
% 1.67/0.58    inference(avatar_sat_refutation,[],[f96,f582,f586])).
% 1.67/0.58  fof(f586,plain,(
% 1.67/0.58    spl3_2),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f585])).
% 1.67/0.58  fof(f585,plain,(
% 1.67/0.58    $false | spl3_2),
% 1.67/0.58    inference(subsumption_resolution,[],[f584,f24])).
% 1.67/0.58  fof(f24,plain,(
% 1.67/0.58    v1_relat_1(sK2)),
% 1.67/0.58    inference(cnf_transformation,[],[f21])).
% 1.67/0.58  fof(f21,plain,(
% 1.67/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 1.67/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f20])).
% 1.67/0.58  fof(f20,plain,(
% 1.67/0.58    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f13,plain,(
% 1.67/0.58    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.67/0.58    inference(flattening,[],[f12])).
% 1.67/0.58  fof(f12,plain,(
% 1.67/0.58    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.67/0.58    inference(ennf_transformation,[],[f11])).
% 1.67/0.58  fof(f11,negated_conjecture,(
% 1.67/0.58    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 1.67/0.58    inference(negated_conjecture,[],[f10])).
% 1.67/0.58  fof(f10,conjecture,(
% 1.67/0.58    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).
% 1.67/0.58  fof(f584,plain,(
% 1.67/0.58    ~v1_relat_1(sK2) | spl3_2),
% 1.67/0.58    inference(resolution,[],[f95,f98])).
% 1.67/0.58  fof(f98,plain,(
% 1.67/0.58    ( ! [X4,X5,X3] : (r1_tarski(k9_relat_1(X3,k1_setfam_1(k1_enumset1(X4,X4,X5))),k9_relat_1(X3,X4)) | ~v1_relat_1(X3)) )),
% 1.67/0.58    inference(resolution,[],[f42,f43])).
% 1.67/0.58  fof(f43,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | r1_tarski(X0,X1)) )),
% 1.67/0.58    inference(definition_unfolding,[],[f36,f38])).
% 1.67/0.58  fof(f38,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.67/0.58    inference(definition_unfolding,[],[f30,f29])).
% 1.67/0.58  fof(f29,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f6])).
% 1.67/0.58  fof(f6,axiom,(
% 1.67/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.67/0.58  fof(f30,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f7])).
% 1.67/0.58  fof(f7,axiom,(
% 1.67/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.67/0.58  fof(f36,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f17])).
% 1.67/0.58  fof(f17,plain,(
% 1.67/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.67/0.58    inference(ennf_transformation,[],[f3])).
% 1.67/0.58  fof(f3,axiom,(
% 1.67/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 1.67/0.58  fof(f42,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k1_setfam_1(k1_enumset1(X0,X0,X1))),k1_setfam_1(k1_enumset1(k9_relat_1(X2,X0),k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) | ~v1_relat_1(X2)) )),
% 1.67/0.58    inference(definition_unfolding,[],[f35,f38,f38])).
% 1.67/0.58  fof(f35,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f16])).
% 1.67/0.58  fof(f16,plain,(
% 1.67/0.58    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) | ~v1_relat_1(X2))),
% 1.67/0.58    inference(ennf_transformation,[],[f8])).
% 1.67/0.58  fof(f8,axiom,(
% 1.67/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,X1)),k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).
% 1.67/0.58  fof(f95,plain,(
% 1.67/0.58    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) | spl3_2),
% 1.67/0.58    inference(avatar_component_clause,[],[f93])).
% 1.67/0.58  fof(f93,plain,(
% 1.67/0.58    spl3_2 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0))),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.67/0.58  fof(f582,plain,(
% 1.67/0.58    spl3_1),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f571])).
% 1.67/0.58  fof(f571,plain,(
% 1.67/0.58    $false | spl3_1),
% 1.67/0.58    inference(resolution,[],[f507,f91])).
% 1.67/0.58  fof(f91,plain,(
% 1.67/0.58    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1) | spl3_1),
% 1.67/0.58    inference(avatar_component_clause,[],[f89])).
% 1.67/0.58  fof(f89,plain,(
% 1.67/0.58    spl3_1 <=> r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.67/0.58  fof(f507,plain,(
% 1.67/0.58    ( ! [X2,X3] : (r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(sK2,X3)))),X3)) )),
% 1.67/0.58    inference(subsumption_resolution,[],[f488,f24])).
% 1.67/0.58  fof(f488,plain,(
% 1.67/0.58    ( ! [X2,X3] : (r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(sK2,X3)))),X3) | ~v1_relat_1(sK2)) )),
% 1.67/0.58    inference(resolution,[],[f426,f97])).
% 1.67/0.58  fof(f97,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))),k9_relat_1(X0,X2)) | ~v1_relat_1(X0)) )),
% 1.67/0.58    inference(resolution,[],[f42,f57])).
% 1.67/0.58  fof(f57,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X2,k1_setfam_1(k1_enumset1(X1,X1,X0))) | r1_tarski(X2,X0)) )),
% 1.67/0.58    inference(superposition,[],[f43,f41])).
% 1.67/0.58  fof(f41,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.67/0.58    inference(definition_unfolding,[],[f28,f29,f29])).
% 1.67/0.58  fof(f28,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f5])).
% 1.67/0.58  fof(f5,axiom,(
% 1.67/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.67/0.58  fof(f426,plain,(
% 1.67/0.58    ( ! [X4,X3] : (~r1_tarski(X4,k9_relat_1(sK2,k10_relat_1(sK2,X3))) | r1_tarski(X4,X3)) )),
% 1.67/0.58    inference(superposition,[],[f43,f423])).
% 1.67/0.58  fof(f423,plain,(
% 1.67/0.58    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k10_relat_1(sK2,X0))))) )),
% 1.67/0.58    inference(subsumption_resolution,[],[f422,f24])).
% 1.67/0.58  fof(f422,plain,(
% 1.67/0.58    ( ! [X0] : (k9_relat_1(sK2,k10_relat_1(sK2,X0)) = k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(sK2,k10_relat_1(sK2,X0)))) | ~v1_relat_1(sK2)) )),
% 1.67/0.58    inference(resolution,[],[f127,f25])).
% 1.67/0.58  fof(f25,plain,(
% 1.67/0.58    v1_funct_1(sK2)),
% 1.67/0.58    inference(cnf_transformation,[],[f21])).
% 1.67/0.58  fof(f127,plain,(
% 1.67/0.58    ( ! [X8,X9] : (~v1_funct_1(X8) | k9_relat_1(X8,k10_relat_1(X8,X9)) = k1_setfam_1(k1_enumset1(X9,X9,k9_relat_1(X8,k10_relat_1(X8,X9)))) | ~v1_relat_1(X8)) )),
% 1.67/0.58    inference(forward_demodulation,[],[f118,f41])).
% 1.67/0.58  fof(f118,plain,(
% 1.67/0.58    ( ! [X8,X9] : (k9_relat_1(X8,k10_relat_1(X8,X9)) = k1_setfam_1(k1_enumset1(k9_relat_1(X8,k10_relat_1(X8,X9)),k9_relat_1(X8,k10_relat_1(X8,X9)),X9)) | ~v1_funct_1(X8) | ~v1_relat_1(X8)) )),
% 1.67/0.58    inference(resolution,[],[f113,f31])).
% 1.67/0.58  fof(f31,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f15])).
% 1.67/0.58  fof(f15,plain,(
% 1.67/0.58    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.67/0.58    inference(flattening,[],[f14])).
% 1.67/0.58  fof(f14,plain,(
% 1.67/0.58    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.67/0.58    inference(ennf_transformation,[],[f9])).
% 1.67/0.58  fof(f9,axiom,(
% 1.67/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.67/0.58  fof(f113,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0) )),
% 1.67/0.58    inference(subsumption_resolution,[],[f110,f45])).
% 1.67/0.58  fof(f45,plain,(
% 1.67/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.67/0.58    inference(equality_resolution,[],[f33])).
% 1.67/0.58  fof(f33,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.67/0.58    inference(cnf_transformation,[],[f23])).
% 1.67/0.58  fof(f23,plain,(
% 1.67/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.67/0.58    inference(flattening,[],[f22])).
% 1.67/0.58  fof(f22,plain,(
% 1.67/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.67/0.58    inference(nnf_transformation,[],[f1])).
% 1.67/0.58  fof(f1,axiom,(
% 1.67/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.67/0.58  fof(f110,plain,(
% 1.67/0.58    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X0)) )),
% 1.67/0.58    inference(resolution,[],[f48,f44])).
% 1.67/0.58  fof(f44,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.67/0.58    inference(definition_unfolding,[],[f37,f38])).
% 1.67/0.58  fof(f37,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f19])).
% 1.67/0.58  fof(f19,plain,(
% 1.67/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.67/0.58    inference(flattening,[],[f18])).
% 1.67/0.58  fof(f18,plain,(
% 1.67/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.67/0.58    inference(ennf_transformation,[],[f4])).
% 1.67/0.58  fof(f4,axiom,(
% 1.67/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.67/0.58  fof(f48,plain,(
% 1.67/0.58    ( ! [X2,X1] : (~r1_tarski(X1,k1_setfam_1(k1_enumset1(X1,X1,X2))) | k1_setfam_1(k1_enumset1(X1,X1,X2)) = X1) )),
% 1.67/0.58    inference(resolution,[],[f34,f40])).
% 1.67/0.58  fof(f40,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 1.67/0.58    inference(definition_unfolding,[],[f27,f38])).
% 1.67/0.58  fof(f27,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f2])).
% 1.67/0.58  fof(f2,axiom,(
% 1.67/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.67/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.67/0.58  fof(f34,plain,(
% 1.67/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f23])).
% 1.67/0.58  fof(f96,plain,(
% 1.67/0.58    ~spl3_1 | ~spl3_2),
% 1.67/0.58    inference(avatar_split_clause,[],[f87,f93,f89])).
% 1.67/0.58  fof(f87,plain,(
% 1.67/0.58    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k9_relat_1(sK2,sK0)) | ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),sK1)),
% 1.67/0.58    inference(resolution,[],[f86,f44])).
% 1.67/0.58  fof(f86,plain,(
% 1.67/0.58    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0))))),
% 1.67/0.58    inference(forward_demodulation,[],[f39,f41])).
% 1.67/0.58  fof(f39,plain,(
% 1.67/0.58    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))),
% 1.67/0.58    inference(definition_unfolding,[],[f26,f38,f38])).
% 1.67/0.58  fof(f26,plain,(
% 1.67/0.58    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 1.67/0.58    inference(cnf_transformation,[],[f21])).
% 1.67/0.58  % SZS output end Proof for theBenchmark
% 1.67/0.58  % (24672)------------------------------
% 1.67/0.58  % (24672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (24672)Termination reason: Refutation
% 1.67/0.58  
% 1.67/0.58  % (24672)Memory used [KB]: 11257
% 1.67/0.58  % (24672)Time elapsed: 0.122 s
% 1.67/0.58  % (24672)------------------------------
% 1.67/0.58  % (24672)------------------------------
% 1.67/0.58  % (24694)Refutation not found, incomplete strategy% (24694)------------------------------
% 1.67/0.58  % (24694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.58  % (24694)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.58  
% 1.67/0.58  % (24694)Memory used [KB]: 10618
% 1.67/0.58  % (24694)Time elapsed: 0.161 s
% 1.67/0.58  % (24694)------------------------------
% 1.67/0.58  % (24694)------------------------------
% 1.67/0.58  % (24665)Success in time 0.216 s
%------------------------------------------------------------------------------
