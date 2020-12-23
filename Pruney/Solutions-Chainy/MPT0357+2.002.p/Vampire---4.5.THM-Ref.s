%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 115 expanded)
%              Number of leaves         :   17 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 283 expanded)
%              Number of equality atoms :   20 (  42 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f64,f69,f89,f100])).

fof(f100,plain,
    ( spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f98,f52])).

fof(f52,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_4
  <=> r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f98,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f92,f68])).

fof(f68,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_6
  <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f92,plain,
    ( r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f88,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0)))
      | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1) ) ),
    inference(superposition,[],[f32,f30])).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f22,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))
      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f27,f25,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f88,plain,
    ( r1_tarski(sK0,k3_tarski(k1_enumset1(sK1,sK1,sK2)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_7
  <=> r1_tarski(sK0,k3_tarski(k1_enumset1(sK1,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f89,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f72,f61,f45,f86])).

fof(f45,plain,
    ( spl3_3
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f61,plain,
    ( spl3_5
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f72,plain,
    ( r1_tarski(sK0,k3_tarski(k1_enumset1(sK1,sK1,sK2)))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f47,f70])).

fof(f70,plain,
    ( ! [X0] :
        ( r1_tarski(sK0,k3_tarski(k1_enumset1(sK1,sK1,X0)))
        | ~ r1_tarski(k3_subset_1(sK0,sK1),X0) )
    | ~ spl3_5 ),
    inference(superposition,[],[f33,f63])).

fof(f63,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
      | r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ) ),
    inference(definition_unfolding,[],[f28,f29,f25])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f47,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f69,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f55,f40,f66])).

fof(f40,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f55,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f42,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f64,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f54,f35,f61])).

fof(f35,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f54,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f37,f31])).

fof(f37,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f53,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f21,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    & r1_tarski(k3_subset_1(sK0,sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f16,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
            & r1_tarski(k3_subset_1(X0,X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,X2),sK1)
          & r1_tarski(k3_subset_1(sK0,sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,X2),sK1)
        & r1_tarski(k3_subset_1(sK0,sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
      & r1_tarski(k3_subset_1(sK0,sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(k3_subset_1(X0,X1),X2)
             => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

fof(f48,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f40])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:59:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (17509)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (17509)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f64,f69,f89,f100])).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    spl3_4 | ~spl3_6 | ~spl3_7),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f99])).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    $false | (spl3_4 | ~spl3_6 | ~spl3_7)),
% 0.22/0.47    inference(subsumption_resolution,[],[f98,f52])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ~r1_tarski(k3_subset_1(sK0,sK2),sK1) | spl3_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f50])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    spl3_4 <=> r1_tarski(k3_subset_1(sK0,sK2),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    r1_tarski(k3_subset_1(sK0,sK2),sK1) | (~spl3_6 | ~spl3_7)),
% 0.22/0.47    inference(forward_demodulation,[],[f92,f68])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl3_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f66])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    spl3_6 <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) | ~spl3_7),
% 0.22/0.47    inference(resolution,[],[f88,f58])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_tarski(k1_enumset1(X1,X1,X0))) | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X0)),X1)) )),
% 0.22/0.47    inference(superposition,[],[f32,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f22,f23,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2))) | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f27,f25,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f24,f23])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    r1_tarski(sK0,k3_tarski(k1_enumset1(sK1,sK1,sK2))) | ~spl3_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f86])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    spl3_7 <=> r1_tarski(sK0,k3_tarski(k1_enumset1(sK1,sK1,sK2)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    spl3_7 | ~spl3_3 | ~spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f72,f61,f45,f86])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    spl3_3 <=> r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    spl3_5 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    r1_tarski(sK0,k3_tarski(k1_enumset1(sK1,sK1,sK2))) | (~spl3_3 | ~spl3_5)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f47,f70])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(sK0,k3_tarski(k1_enumset1(sK1,sK1,X0))) | ~r1_tarski(k3_subset_1(sK0,sK1),X0)) ) | ~spl3_5),
% 0.22/0.47    inference(superposition,[],[f33,f63])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f61])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) | r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f28,f29,f25])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    r1_tarski(k3_subset_1(sK0,sK1),sK2) | ~spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f45])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    spl3_6 | ~spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f55,f40,f66])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl3_2),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f42,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 0.22/0.47    inference(definition_unfolding,[],[f26,f25])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f40])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    spl3_5 | ~spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f54,f35,f61])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_1),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f37,f31])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f35])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ~spl3_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f21,f50])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ~r1_tarski(k3_subset_1(sK0,sK2),sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    (~r1_tarski(k3_subset_1(sK0,sK2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f16,f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,X2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ? [X2] : (~r1_tarski(k3_subset_1(sK0,X2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,sK2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.47    inference(flattening,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 0.22/0.47    inference(negated_conjecture,[],[f8])).
% 0.22/0.47  fof(f8,conjecture,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f20,f45])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f19,f40])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f18,f35])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (17509)------------------------------
% 0.22/0.47  % (17509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (17509)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (17509)Memory used [KB]: 10618
% 0.22/0.47  % (17509)Time elapsed: 0.010 s
% 0.22/0.47  % (17509)------------------------------
% 0.22/0.47  % (17509)------------------------------
% 0.22/0.47  % (17487)Success in time 0.111 s
%------------------------------------------------------------------------------
