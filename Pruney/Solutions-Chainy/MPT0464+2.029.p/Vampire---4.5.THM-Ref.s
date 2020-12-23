%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:29 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 164 expanded)
%              Number of leaves         :   14 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  197 ( 499 expanded)
%              Number of equality atoms :   14 (  54 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (5349)Termination reason: Refutation not found, incomplete strategy

fof(f116,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f85,f115])).

fof(f115,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f111,f24])).

fof(f24,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

% (5349)Memory used [KB]: 10618
% (5349)Time elapsed: 0.142 s
% (5349)------------------------------
% (5349)------------------------------
fof(f20,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
                & v1_relat_1(X2) )
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2)))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

fof(f111,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_2 ),
    inference(resolution,[],[f101,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f101,plain,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | spl3_2 ),
    inference(subsumption_resolution,[],[f100,f23])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f100,plain,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f99,f25])).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f99,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f98,f43])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f98,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f97,f48])).

fof(f48,plain,(
    ! [X2,X3] : r1_tarski(k1_setfam_1(k1_enumset1(X3,X3,X2)),X2) ),
    inference(superposition,[],[f39,f40])).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f29,f30,f30])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f97,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK2)
    | ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | spl3_2 ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK2)
    | ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_2 ),
    inference(resolution,[],[f67,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).

fof(f67,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_2
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f85,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f81,f24])).

fof(f81,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_1 ),
    inference(resolution,[],[f79,f41])).

fof(f79,plain,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f78,f23])).

fof(f78,plain,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f77,f24])).

fof(f77,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f76,f43])).

fof(f76,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f75,f39])).

fof(f75,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK1)
    | ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK1)
    | ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(resolution,[],[f27,f63])).

fof(f63,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_1
  <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f68,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f59,f65,f61])).

fof(f59,plain,
    ( ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK2))
    | ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f38,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f38,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f26,f37,f37])).

fof(f26,plain,(
    ~ r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:17:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (5333)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (5343)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (5339)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.56  % (5341)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.56  % (5343)Refutation not found, incomplete strategy% (5343)------------------------------
% 1.39/0.56  % (5343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (5335)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.39/0.57  % (5337)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.39/0.57  % (5343)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.57  
% 1.39/0.57  % (5343)Memory used [KB]: 10746
% 1.39/0.57  % (5343)Time elapsed: 0.132 s
% 1.39/0.57  % (5343)------------------------------
% 1.39/0.57  % (5343)------------------------------
% 1.39/0.57  % (5349)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.57  % (5338)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.39/0.57  % (5349)Refutation not found, incomplete strategy% (5349)------------------------------
% 1.39/0.57  % (5349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (5356)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.58  % (5339)Refutation found. Thanks to Tanya!
% 1.39/0.58  % SZS status Theorem for theBenchmark
% 1.39/0.58  % SZS output start Proof for theBenchmark
% 1.39/0.58  % (5349)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.58  
% 1.39/0.58  fof(f116,plain,(
% 1.39/0.58    $false),
% 1.39/0.58    inference(avatar_sat_refutation,[],[f68,f85,f115])).
% 1.39/0.58  fof(f115,plain,(
% 1.39/0.58    spl3_2),
% 1.39/0.58    inference(avatar_contradiction_clause,[],[f114])).
% 1.39/0.58  fof(f114,plain,(
% 1.39/0.58    $false | spl3_2),
% 1.39/0.58    inference(subsumption_resolution,[],[f111,f24])).
% 1.39/0.58  fof(f24,plain,(
% 1.39/0.58    v1_relat_1(sK1)),
% 1.39/0.58    inference(cnf_transformation,[],[f20])).
% 1.39/0.58  % (5349)Memory used [KB]: 10618
% 1.39/0.58  % (5349)Time elapsed: 0.142 s
% 1.39/0.58  % (5349)------------------------------
% 1.39/0.58  % (5349)------------------------------
% 1.39/0.58  fof(f20,plain,(
% 1.39/0.58    ((~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.39/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19,f18,f17])).
% 1.39/0.58  fof(f17,plain,(
% 1.39/0.58    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.39/0.58    introduced(choice_axiom,[])).
% 1.39/0.58  fof(f18,plain,(
% 1.39/0.58    ? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(sK0,X1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 1.39/0.58    introduced(choice_axiom,[])).
% 1.39/0.58  fof(f19,plain,(
% 1.39/0.58    ? [X2] : (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,X2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,X2))) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))) & v1_relat_1(sK2))),
% 1.39/0.58    introduced(choice_axiom,[])).
% 1.39/0.58  fof(f11,plain,(
% 1.39/0.58    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.39/0.58    inference(ennf_transformation,[],[f10])).
% 1.39/0.58  fof(f10,negated_conjecture,(
% 1.39/0.58    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.39/0.58    inference(negated_conjecture,[],[f9])).
% 1.39/0.58  fof(f9,conjecture,(
% 1.39/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).
% 1.39/0.58  fof(f111,plain,(
% 1.39/0.58    ~v1_relat_1(sK1) | spl3_2),
% 1.39/0.58    inference(resolution,[],[f101,f41])).
% 1.39/0.58  fof(f41,plain,(
% 1.39/0.58    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 1.39/0.58    inference(definition_unfolding,[],[f32,f37])).
% 1.39/0.58  fof(f37,plain,(
% 1.39/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.39/0.58    inference(definition_unfolding,[],[f31,f30])).
% 1.39/0.58  fof(f30,plain,(
% 1.39/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f5])).
% 1.39/0.58  fof(f5,axiom,(
% 1.39/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.39/0.58  fof(f31,plain,(
% 1.39/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.39/0.58    inference(cnf_transformation,[],[f6])).
% 1.39/0.58  fof(f6,axiom,(
% 1.39/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.39/0.58  fof(f32,plain,(
% 1.39/0.58    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f14])).
% 1.39/0.58  fof(f14,plain,(
% 1.39/0.58    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.39/0.58    inference(ennf_transformation,[],[f7])).
% 1.39/0.58  fof(f7,axiom,(
% 1.39/0.58    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.39/0.58  fof(f101,plain,(
% 1.39/0.58    ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | spl3_2),
% 1.39/0.58    inference(subsumption_resolution,[],[f100,f23])).
% 1.39/0.58  fof(f23,plain,(
% 1.39/0.58    v1_relat_1(sK0)),
% 1.39/0.58    inference(cnf_transformation,[],[f20])).
% 1.39/0.58  fof(f100,plain,(
% 1.39/0.58    ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK0) | spl3_2),
% 1.39/0.58    inference(subsumption_resolution,[],[f99,f25])).
% 1.39/0.58  fof(f25,plain,(
% 1.39/0.58    v1_relat_1(sK2)),
% 1.39/0.58    inference(cnf_transformation,[],[f20])).
% 1.39/0.58  fof(f99,plain,(
% 1.39/0.58    ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK0) | spl3_2),
% 1.39/0.58    inference(subsumption_resolution,[],[f98,f43])).
% 1.39/0.58  fof(f43,plain,(
% 1.39/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.39/0.58    inference(equality_resolution,[],[f34])).
% 1.39/0.58  fof(f34,plain,(
% 1.39/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.39/0.58    inference(cnf_transformation,[],[f22])).
% 1.39/0.58  fof(f22,plain,(
% 1.39/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.58    inference(flattening,[],[f21])).
% 1.39/0.58  fof(f21,plain,(
% 1.39/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.58    inference(nnf_transformation,[],[f1])).
% 1.39/0.58  fof(f1,axiom,(
% 1.39/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.58  fof(f98,plain,(
% 1.39/0.58    ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK0) | spl3_2),
% 1.39/0.58    inference(subsumption_resolution,[],[f97,f48])).
% 1.39/0.58  fof(f48,plain,(
% 1.39/0.58    ( ! [X2,X3] : (r1_tarski(k1_setfam_1(k1_enumset1(X3,X3,X2)),X2)) )),
% 1.39/0.58    inference(superposition,[],[f39,f40])).
% 1.39/0.58  fof(f40,plain,(
% 1.39/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.39/0.58    inference(definition_unfolding,[],[f29,f30,f30])).
% 1.39/0.58  fof(f29,plain,(
% 1.39/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f4])).
% 1.39/0.58  fof(f4,axiom,(
% 1.39/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.39/0.58  fof(f39,plain,(
% 1.39/0.58    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 1.39/0.58    inference(definition_unfolding,[],[f28,f37])).
% 1.39/0.58  fof(f28,plain,(
% 1.39/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f2])).
% 1.39/0.58  fof(f2,axiom,(
% 1.39/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.39/0.58  fof(f97,plain,(
% 1.39/0.58    ~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK2) | ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK0) | spl3_2),
% 1.39/0.58    inference(duplicate_literal_removal,[],[f96])).
% 1.39/0.58  fof(f96,plain,(
% 1.39/0.58    ~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK2) | ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK0) | ~v1_relat_1(sK0) | spl3_2),
% 1.39/0.58    inference(resolution,[],[f67,f27])).
% 1.39/0.58  fof(f27,plain,(
% 1.39/0.58    ( ! [X2,X0,X3,X1] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f13])).
% 1.39/0.58  fof(f13,plain,(
% 1.39/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.39/0.58    inference(flattening,[],[f12])).
% 1.39/0.58  fof(f12,plain,(
% 1.39/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.39/0.58    inference(ennf_transformation,[],[f8])).
% 1.39/0.58  fof(f8,axiom,(
% 1.39/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)))))))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relat_1)).
% 1.39/0.58  fof(f67,plain,(
% 1.39/0.58    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | spl3_2),
% 1.39/0.58    inference(avatar_component_clause,[],[f65])).
% 1.39/0.58  fof(f65,plain,(
% 1.39/0.58    spl3_2 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK2))),
% 1.39/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.39/0.58  fof(f85,plain,(
% 1.39/0.58    spl3_1),
% 1.39/0.58    inference(avatar_contradiction_clause,[],[f84])).
% 1.39/0.58  fof(f84,plain,(
% 1.39/0.58    $false | spl3_1),
% 1.39/0.58    inference(subsumption_resolution,[],[f81,f24])).
% 1.39/0.58  fof(f81,plain,(
% 1.39/0.58    ~v1_relat_1(sK1) | spl3_1),
% 1.39/0.58    inference(resolution,[],[f79,f41])).
% 1.39/0.58  fof(f79,plain,(
% 1.39/0.58    ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | spl3_1),
% 1.39/0.58    inference(subsumption_resolution,[],[f78,f23])).
% 1.39/0.58  fof(f78,plain,(
% 1.39/0.58    ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK0) | spl3_1),
% 1.39/0.58    inference(subsumption_resolution,[],[f77,f24])).
% 1.39/0.58  fof(f77,plain,(
% 1.39/0.58    ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK0) | spl3_1),
% 1.39/0.58    inference(subsumption_resolution,[],[f76,f43])).
% 1.39/0.58  fof(f76,plain,(
% 1.39/0.58    ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK0) | spl3_1),
% 1.39/0.58    inference(subsumption_resolution,[],[f75,f39])).
% 1.39/0.58  fof(f75,plain,(
% 1.39/0.58    ~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK1) | ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK0) | spl3_1),
% 1.39/0.58    inference(duplicate_literal_removal,[],[f73])).
% 1.39/0.58  fof(f73,plain,(
% 1.39/0.58    ~r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,sK2)),sK1) | ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK1,sK1,sK2))) | ~v1_relat_1(sK0) | ~v1_relat_1(sK0) | spl3_1),
% 1.39/0.58    inference(resolution,[],[f27,f63])).
% 1.39/0.58  fof(f63,plain,(
% 1.39/0.58    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1)) | spl3_1),
% 1.39/0.58    inference(avatar_component_clause,[],[f61])).
% 1.39/0.58  fof(f61,plain,(
% 1.39/0.58    spl3_1 <=> r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 1.39/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.39/0.58  fof(f68,plain,(
% 1.39/0.58    ~spl3_1 | ~spl3_2),
% 1.39/0.58    inference(avatar_split_clause,[],[f59,f65,f61])).
% 1.39/0.58  fof(f59,plain,(
% 1.39/0.58    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK2)) | ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k5_relat_1(sK0,sK1))),
% 1.39/0.58    inference(resolution,[],[f38,f42])).
% 1.39/0.58  fof(f42,plain,(
% 1.39/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.39/0.58    inference(definition_unfolding,[],[f36,f37])).
% 1.39/0.58  fof(f36,plain,(
% 1.39/0.58    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.39/0.58    inference(cnf_transformation,[],[f16])).
% 1.39/0.58  fof(f16,plain,(
% 1.39/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.39/0.58    inference(flattening,[],[f15])).
% 1.39/0.58  fof(f15,plain,(
% 1.39/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.39/0.58    inference(ennf_transformation,[],[f3])).
% 1.39/0.58  fof(f3,axiom,(
% 1.39/0.58    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.39/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.39/0.58  fof(f38,plain,(
% 1.39/0.58    ~r1_tarski(k5_relat_1(sK0,k1_setfam_1(k1_enumset1(sK1,sK1,sK2))),k1_setfam_1(k1_enumset1(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2))))),
% 1.39/0.58    inference(definition_unfolding,[],[f26,f37,f37])).
% 1.39/0.58  fof(f26,plain,(
% 1.39/0.58    ~r1_tarski(k5_relat_1(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k5_relat_1(sK0,sK1),k5_relat_1(sK0,sK2)))),
% 1.39/0.58    inference(cnf_transformation,[],[f20])).
% 1.39/0.58  % SZS output end Proof for theBenchmark
% 1.39/0.58  % (5339)------------------------------
% 1.39/0.58  % (5339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.58  % (5339)Termination reason: Refutation
% 1.39/0.58  
% 1.39/0.58  % (5339)Memory used [KB]: 10746
% 1.39/0.58  % (5339)Time elapsed: 0.147 s
% 1.39/0.58  % (5339)------------------------------
% 1.39/0.58  % (5339)------------------------------
% 1.70/0.58  % (5332)Success in time 0.213 s
%------------------------------------------------------------------------------
