%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 147 expanded)
%              Number of leaves         :   18 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  160 ( 309 expanded)
%              Number of equality atoms :    8 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f79,f89,f91,f93,f97,f99,f101])).

fof(f101,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl2_7 ),
    inference(resolution,[],[f88,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X0) ),
    inference(superposition,[],[f36,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f28,f29,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f88,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_7
  <=> r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f99,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f78,f36])).

fof(f78,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_5
  <=> r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f97,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f94,f22])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18,f17])).

% (22380)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

fof(f94,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_3 ),
    inference(resolution,[],[f70,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f42,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f26,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f70,plain,
    ( ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_3
  <=> v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f93,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f84,f22])).

fof(f84,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f91,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl2_4 ),
    inference(resolution,[],[f74,f21])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl2_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f89,plain,
    ( ~ spl2_3
    | ~ spl2_6
    | ~ spl2_7
    | spl2_2 ),
    inference(avatar_split_clause,[],[f80,f62,f86,f82,f68])).

fof(f62,plain,
    ( spl2_2
  <=> r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f80,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_2 ),
    inference(resolution,[],[f64,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f64,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f79,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_1 ),
    inference(avatar_split_clause,[],[f66,f58,f76,f72,f68])).

fof(f58,plain,
    ( spl2_1
  <=> r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f66,plain,
    ( ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))
    | spl2_1 ),
    inference(resolution,[],[f60,f25])).

fof(f60,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f65,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f54,f62,f58])).

fof(f54,plain,
    ( ~ r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK0)) ),
    inference(resolution,[],[f38,f35])).

fof(f35,plain,(
    ~ r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1)))) ),
    inference(definition_unfolding,[],[f23,f34,f34])).

fof(f23,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:54:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.41  % (22391)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.12/0.41  % (22391)Refutation not found, incomplete strategy% (22391)------------------------------
% 0.12/0.41  % (22391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.41  % (22391)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.41  
% 0.12/0.41  % (22391)Memory used [KB]: 10618
% 0.12/0.41  % (22391)Time elapsed: 0.003 s
% 0.12/0.41  % (22391)------------------------------
% 0.12/0.41  % (22391)------------------------------
% 0.20/0.45  % (22384)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (22397)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.45  % (22384)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f102,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f65,f79,f89,f91,f93,f97,f99,f101])).
% 0.20/0.46  fof(f101,plain,(
% 0.20/0.46    spl2_7),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f100])).
% 0.20/0.46  fof(f100,plain,(
% 0.20/0.46    $false | spl2_7),
% 0.20/0.46    inference(resolution,[],[f88,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X1,X1,X0)),X0)) )),
% 0.20/0.46    inference(superposition,[],[f36,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f28,f29,f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f27,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f30,f29])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1) | spl2_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f86])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    spl2_7 <=> r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    spl2_5),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f98])).
% 0.20/0.46  fof(f98,plain,(
% 0.20/0.46    $false | spl2_5),
% 0.20/0.46    inference(resolution,[],[f78,f36])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0) | spl2_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f76])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    spl2_5 <=> r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.46  fof(f97,plain,(
% 0.20/0.46    spl2_3),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f96])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    $false | spl2_3),
% 0.20/0.46    inference(resolution,[],[f94,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    v1_relat_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18,f17])).
% 0.20/0.46  % (22380)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.20/0.46    inference(negated_conjecture,[],[f9])).
% 0.20/0.46  fof(f9,conjecture,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    ~v1_relat_1(sK1) | spl2_3),
% 0.20/0.46    inference(resolution,[],[f70,f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k1_enumset1(X1,X1,X0))) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(resolution,[],[f42,f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 0.20/0.46    inference(resolution,[],[f26,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.46    inference(nnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    spl2_3 <=> v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    spl2_6),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f92])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    $false | spl2_6),
% 0.20/0.46    inference(resolution,[],[f84,f22])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    ~v1_relat_1(sK1) | spl2_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f82])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    spl2_6 <=> v1_relat_1(sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    spl2_4),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f90])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    $false | spl2_4),
% 0.20/0.46    inference(resolution,[],[f74,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    v1_relat_1(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    ~v1_relat_1(sK0) | spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f72])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    spl2_4 <=> v1_relat_1(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    ~spl2_3 | ~spl2_6 | ~spl2_7 | spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f80,f62,f86,f82,f68])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    spl2_2 <=> r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_2),
% 0.20/0.46    inference(resolution,[],[f64,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(flattening,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    ~r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK1)) | spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f62])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    ~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f66,f58,f76,f72,f68])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    spl2_1 <=> r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    ~r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,sK1)),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) | spl2_1),
% 0.20/0.46    inference(resolution,[],[f60,f25])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    ~r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK0)) | spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f58])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ~spl2_1 | ~spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f54,f62,f58])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ~r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK1)) | ~r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k2_relat_1(sK0))),
% 0.20/0.46    inference(resolution,[],[f38,f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ~r1_tarski(k2_relat_1(k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),k1_setfam_1(k1_enumset1(k2_relat_1(sK0),k2_relat_1(sK0),k2_relat_1(sK1))))),
% 0.20/0.46    inference(definition_unfolding,[],[f23,f34,f34])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 0.20/0.46    inference(cnf_transformation,[],[f19])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f33,f34])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (22384)------------------------------
% 0.20/0.46  % (22384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (22384)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (22384)Memory used [KB]: 6140
% 0.20/0.46  % (22384)Time elapsed: 0.058 s
% 0.20/0.46  % (22384)------------------------------
% 0.20/0.46  % (22384)------------------------------
% 0.20/0.46  % (22379)Success in time 0.103 s
%------------------------------------------------------------------------------
