%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 106 expanded)
%              Number of leaves         :   17 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 199 expanded)
%              Number of equality atoms :   49 (  80 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f97,f119,f125,f127,f148])).

fof(f148,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f132,f22])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f132,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl2_5 ),
    inference(trivial_inequality_removal,[],[f130])).

fof(f130,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | spl2_5 ),
    inference(superposition,[],[f118,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f118,plain,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl2_5
  <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f127,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f114,f36])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f114,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl2_4
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f125,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f110,f22])).

fof(f110,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_3
  <=> v1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f119,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f106,f92,f116,f112,f108])).

fof(f92,plain,
    ( spl2_2
  <=> ! [X0] :
        ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k7_relat_1(k6_relat_1(X0),sK0),sK1)
        | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),X0)
        | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f106,plain,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl2_2 ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl2_2 ),
    inference(superposition,[],[f93,f43])).

fof(f43,plain,(
    ! [X2] :
      ( k6_relat_1(X2) = k7_relat_1(k6_relat_1(X2),X2)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f42])).

fof(f42,plain,(
    ! [X2] :
      ( ~ v1_relat_1(k6_relat_1(X2))
      | k6_relat_1(X2) = k7_relat_1(k6_relat_1(X2),X2)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(forward_demodulation,[],[f41,f24])).

fof(f24,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f41,plain,(
    ! [X2] :
      ( k6_relat_1(X2) = k7_relat_1(k6_relat_1(X2),X2)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X2))))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(forward_demodulation,[],[f39,f24])).

fof(f39,plain,(
    ! [X2] :
      ( k6_relat_1(X2) = k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X2))),X2)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X2))))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f29,f25])).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f93,plain,
    ( ! [X0] :
        ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k7_relat_1(k6_relat_1(X0),sK0),sK1)
        | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),X0)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f97,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f90,f22])).

fof(f90,plain,
    ( ~ v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_1
  <=> v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f94,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f74,f92,f88])).

fof(f74,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k7_relat_1(k6_relat_1(X0),sK0),sK1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),X0)
      | ~ v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) ) ),
    inference(superposition,[],[f35,f61])).

fof(f61,plain,(
    ! [X2,X3,X1] :
      ( k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X1)
      | ~ v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))) ) ),
    inference(duplicate_literal_removal,[],[f60])).

fof(f60,plain,(
    ! [X2,X3,X1] :
      ( k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X1)
      | ~ v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3))))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f37,f49])).

fof(f49,plain,(
    ! [X4,X3] :
      ( k6_relat_1(X3) = k7_relat_1(k6_relat_1(X4),X3)
      | ~ r1_tarski(X3,X4)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(forward_demodulation,[],[f47,f24])).

fof(f47,plain,(
    ! [X4,X3] :
      ( k6_relat_1(X3) = k7_relat_1(k6_relat_1(X4),X3)
      | ~ r1_tarski(k2_relat_1(k6_relat_1(X3)),X4)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(superposition,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f35,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f21,f34])).

fof(f21,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f19])).

fof(f19,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:25:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (14629)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (14629)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f149,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f94,f97,f119,f125,f127,f148])).
% 0.22/0.46  fof(f148,plain,(
% 0.22/0.46    spl2_5),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f147])).
% 0.22/0.46  fof(f147,plain,(
% 0.22/0.46    $false | spl2_5),
% 0.22/0.46    inference(resolution,[],[f132,f22])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.46  fof(f132,plain,(
% 0.22/0.46    ~v1_relat_1(k6_relat_1(sK0)) | spl2_5),
% 0.22/0.46    inference(trivial_inequality_removal,[],[f130])).
% 0.22/0.46  fof(f130,plain,(
% 0.22/0.46    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) | ~v1_relat_1(k6_relat_1(sK0)) | spl2_5),
% 0.22/0.46    inference(superposition,[],[f118,f29])).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f10])).
% 0.22/0.46  fof(f10,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.46  fof(f118,plain,(
% 0.22/0.46    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k6_relat_1(sK0),sK1) | spl2_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f116])).
% 0.22/0.46  fof(f116,plain,(
% 0.22/0.46    spl2_5 <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.46  fof(f127,plain,(
% 0.22/0.46    spl2_4),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f126])).
% 0.22/0.46  fof(f126,plain,(
% 0.22/0.46    $false | spl2_4),
% 0.22/0.46    inference(resolution,[],[f114,f36])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f26,f34])).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.46    inference(definition_unfolding,[],[f27,f33])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f28,f31])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.46  fof(f114,plain,(
% 0.22/0.46    ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | spl2_4),
% 0.22/0.46    inference(avatar_component_clause,[],[f112])).
% 0.22/0.46  fof(f112,plain,(
% 0.22/0.46    spl2_4 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.46  fof(f125,plain,(
% 0.22/0.46    spl2_3),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f124])).
% 0.22/0.46  fof(f124,plain,(
% 0.22/0.46    $false | spl2_3),
% 0.22/0.46    inference(resolution,[],[f110,f22])).
% 0.22/0.46  fof(f110,plain,(
% 0.22/0.46    ~v1_relat_1(k6_relat_1(sK0)) | spl2_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f108])).
% 0.22/0.46  fof(f108,plain,(
% 0.22/0.46    spl2_3 <=> v1_relat_1(k6_relat_1(sK0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.46  fof(f119,plain,(
% 0.22/0.46    ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f106,f92,f116,f112,f108])).
% 0.22/0.46  fof(f92,plain,(
% 0.22/0.46    spl2_2 <=> ! [X0] : (k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k7_relat_1(k6_relat_1(X0),sK0),sK1) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),X0) | ~v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.46  fof(f106,plain,(
% 0.22/0.46    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k6_relat_1(sK0),sK1) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | ~v1_relat_1(k6_relat_1(sK0)) | ~spl2_2),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f99])).
% 0.22/0.46  fof(f99,plain,(
% 0.22/0.46    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k6_relat_1(sK0),sK1) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),sK0) | ~v1_relat_1(k6_relat_1(sK0)) | ~v1_relat_1(k6_relat_1(sK0)) | ~spl2_2),
% 0.22/0.46    inference(superposition,[],[f93,f43])).
% 0.22/0.46  fof(f43,plain,(
% 0.22/0.46    ( ! [X2] : (k6_relat_1(X2) = k7_relat_1(k6_relat_1(X2),X2) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f42])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    ( ! [X2] : (~v1_relat_1(k6_relat_1(X2)) | k6_relat_1(X2) = k7_relat_1(k6_relat_1(X2),X2) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.22/0.46    inference(forward_demodulation,[],[f41,f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.46    inference(cnf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,axiom,(
% 0.22/0.46    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.46  fof(f41,plain,(
% 0.22/0.46    ( ! [X2] : (k6_relat_1(X2) = k7_relat_1(k6_relat_1(X2),X2) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X2)))) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.22/0.46    inference(forward_demodulation,[],[f39,f24])).
% 0.22/0.46  fof(f39,plain,(
% 0.22/0.46    ( ! [X2] : (k6_relat_1(X2) = k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X2))),X2) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(X2)))) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.22/0.46    inference(superposition,[],[f29,f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,axiom,(
% 0.22/0.46    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.22/0.46  fof(f93,plain,(
% 0.22/0.46    ( ! [X0] : (k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k7_relat_1(k6_relat_1(X0),sK0),sK1) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),X0) | ~v1_relat_1(k6_relat_1(X0))) ) | ~spl2_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f92])).
% 0.22/0.46  fof(f97,plain,(
% 0.22/0.46    spl2_1),
% 0.22/0.46    inference(avatar_contradiction_clause,[],[f95])).
% 0.22/0.46  fof(f95,plain,(
% 0.22/0.46    $false | spl2_1),
% 0.22/0.46    inference(resolution,[],[f90,f22])).
% 0.22/0.46  fof(f90,plain,(
% 0.22/0.46    ~v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))) | spl2_1),
% 0.22/0.46    inference(avatar_component_clause,[],[f88])).
% 0.22/0.46  fof(f88,plain,(
% 0.22/0.46    spl2_1 <=> v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.46  fof(f94,plain,(
% 0.22/0.46    ~spl2_1 | spl2_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f74,f92,f88])).
% 0.22/0.46  fof(f74,plain,(
% 0.22/0.46    ( ! [X0] : (k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k7_relat_1(k7_relat_1(k6_relat_1(X0),sK0),sK1) | ~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)),X0) | ~v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))))) )),
% 0.22/0.46    inference(superposition,[],[f35,f61])).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    ( ! [X2,X3,X1] : (k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) | ~v1_relat_1(k6_relat_1(X1)) | ~r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X1) | ~v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3))))) )),
% 0.22/0.46    inference(duplicate_literal_removal,[],[f60])).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    ( ! [X2,X3,X1] : (k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3) | ~v1_relat_1(k6_relat_1(X1)) | ~r1_tarski(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)),X1) | ~v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3)))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.22/0.46    inference(superposition,[],[f37,f49])).
% 0.22/0.46  fof(f49,plain,(
% 0.22/0.46    ( ! [X4,X3] : (k6_relat_1(X3) = k7_relat_1(k6_relat_1(X4),X3) | ~r1_tarski(X3,X4) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X4))) )),
% 0.22/0.46    inference(forward_demodulation,[],[f47,f24])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    ( ! [X4,X3] : (k6_relat_1(X3) = k7_relat_1(k6_relat_1(X4),X3) | ~r1_tarski(k2_relat_1(k6_relat_1(X3)),X4) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X4))) )),
% 0.22/0.46    inference(superposition,[],[f30,f29])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(flattening,[],[f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,axiom,(
% 0.22/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f32,f34])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f18])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.46    inference(ennf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.22/0.46    inference(definition_unfolding,[],[f21,f34])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,negated_conjecture,(
% 0.22/0.46    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.46    inference(negated_conjecture,[],[f11])).
% 0.22/0.46  fof(f11,conjecture,(
% 0.22/0.46    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (14629)------------------------------
% 0.22/0.46  % (14629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (14629)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (14629)Memory used [KB]: 6140
% 0.22/0.46  % (14629)Time elapsed: 0.046 s
% 0.22/0.46  % (14629)------------------------------
% 0.22/0.46  % (14629)------------------------------
% 0.22/0.46  % (14625)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (14633)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (14631)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (14628)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (14624)Success in time 0.114 s
%------------------------------------------------------------------------------
