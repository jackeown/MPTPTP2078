%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 153 expanded)
%              Number of leaves         :   18 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  207 ( 446 expanded)
%              Number of equality atoms :   45 ( 119 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f105,f111,f125,f150,f156,f183])).

fof(f183,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_11 ),
    inference(subsumption_resolution,[],[f178,f110])).

fof(f110,plain,
    ( r1_xboole_0(sK2,k3_subset_1(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_6
  <=> r1_xboole_0(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f178,plain,
    ( ~ r1_xboole_0(sK2,k3_subset_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f54,f59,f155,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f155,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_11
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f59,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f54,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f156,plain,
    ( ~ spl3_11
    | spl3_1
    | spl3_9 ),
    inference(avatar_split_clause,[],[f151,f138,f42,f153])).

fof(f42,plain,
    ( spl3_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f138,plain,
    ( spl3_9
  <=> r2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f151,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl3_1
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f44,f140,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f140,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f44,plain,
    ( sK1 != sK2
    | spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f150,plain,
    ( ~ spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f131,f120,f138])).

fof(f120,plain,
    ( spl3_7
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f131,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f122,f77])).

fof(f77,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ r2_xboole_0(X4,X3) ) ),
    inference(trivial_inequality_removal,[],[f76])).

fof(f76,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_xboole_0(X4,X3)
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f39,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != k1_xboole_0
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != k1_xboole_0
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( k4_xboole_0(X1,X0) = k1_xboole_0
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

fof(f122,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f120])).

fof(f125,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f124,f102,f57,f52,f47,f120])).

fof(f47,plain,
    ( spl3_2
  <=> k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f102,plain,
    ( spl3_5
  <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f124,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f116,f59])).

fof(f116,plain,
    ( r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f104,f93])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k3_subset_1(sK0,sK1))
        | r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f92,f54])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k3_subset_1(sK0,sK1))
        | r1_tarski(X0,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl3_2 ),
    inference(superposition,[],[f32,f49])).

fof(f49,plain,
    ( k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f104,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f111,plain,
    ( spl3_6
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f106,f52,f47,f108])).

fof(f106,plain,
    ( r1_xboole_0(sK2,k3_subset_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f94,f49])).

fof(f94,plain,
    ( r1_xboole_0(sK2,k3_subset_1(sK0,sK2))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f63,f54,f54,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(unit_resulting_resolution,[],[f61,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f29,f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f105,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f95,f57,f102])).

fof(f95,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f63,f59,f59,f33])).

fof(f60,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK1 != sK2
    & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k3_subset_1(X0,X2) = k3_subset_1(X0,X1)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != X2
          & k3_subset_1(sK0,X2) = k3_subset_1(sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k3_subset_1(sK0,X2) = k3_subset_1(sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != sK2
      & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X2) = k3_subset_1(X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X2) = k3_subset_1(X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( k3_subset_1(X0,X2) = k3_subset_1(X0,X1)
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( k3_subset_1(X0,X2) = k3_subset_1(X0,X1)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_subset_1)).

fof(f55,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f47])).

fof(f26,plain,(
    k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f27,f42])).

fof(f27,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:07:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.45  % (13902)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (13902)Refutation not found, incomplete strategy% (13902)------------------------------
% 0.22/0.47  % (13902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (13902)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (13902)Memory used [KB]: 10618
% 0.22/0.47  % (13902)Time elapsed: 0.072 s
% 0.22/0.47  % (13902)------------------------------
% 0.22/0.47  % (13902)------------------------------
% 0.22/0.47  % (13917)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.47  % (13911)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.47  % (13914)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (13909)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (13914)Refutation not found, incomplete strategy% (13914)------------------------------
% 0.22/0.48  % (13914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (13914)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (13914)Memory used [KB]: 1663
% 0.22/0.48  % (13914)Time elapsed: 0.052 s
% 0.22/0.48  % (13914)------------------------------
% 0.22/0.48  % (13914)------------------------------
% 0.22/0.48  % (13905)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (13910)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (13906)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (13917)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f184,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f45,f50,f55,f60,f105,f111,f125,f150,f156,f183])).
% 0.22/0.48  fof(f183,plain,(
% 0.22/0.48    ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_11),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f182])).
% 0.22/0.48  fof(f182,plain,(
% 0.22/0.48    $false | (~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_11)),
% 0.22/0.48    inference(subsumption_resolution,[],[f178,f110])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    r1_xboole_0(sK2,k3_subset_1(sK0,sK1)) | ~spl3_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f108])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    spl3_6 <=> r1_xboole_0(sK2,k3_subset_1(sK0,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f178,plain,(
% 0.22/0.48    ~r1_xboole_0(sK2,k3_subset_1(sK0,sK1)) | (~spl3_3 | ~spl3_4 | spl3_11)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f54,f59,f155,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,k3_subset_1(X0,X2)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(nnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    ~r1_tarski(sK2,sK1) | spl3_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f153])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    spl3_11 <=> r1_tarski(sK2,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    ~spl3_11 | spl3_1 | spl3_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f151,f138,f42,f153])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    spl3_1 <=> sK1 = sK2),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    spl3_9 <=> r2_xboole_0(sK2,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    ~r1_tarski(sK2,sK1) | (spl3_1 | spl3_9)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f44,f140,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.48    inference(flattening,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    ~r2_xboole_0(sK2,sK1) | spl3_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f138])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    sK1 != sK2 | spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f42])).
% 0.22/0.48  fof(f150,plain,(
% 0.22/0.48    ~spl3_9 | ~spl3_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f131,f120,f138])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    spl3_7 <=> r1_tarski(sK1,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    ~r2_xboole_0(sK2,sK1) | ~spl3_7),
% 0.22/0.48    inference(resolution,[],[f122,f77])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ( ! [X4,X3] : (~r1_tarski(X3,X4) | ~r2_xboole_0(X4,X3)) )),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ( ! [X4,X3] : (k1_xboole_0 != k1_xboole_0 | ~r2_xboole_0(X4,X3) | ~r1_tarski(X3,X4)) )),
% 0.22/0.48    inference(superposition,[],[f39,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X1,X0) != k1_xboole_0 | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : (k4_xboole_0(X1,X0) != k1_xboole_0 | ~r2_xboole_0(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : ~(k4_xboole_0(X1,X0) = k1_xboole_0 & r2_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    r1_tarski(sK1,sK2) | ~spl3_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f120])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    spl3_7 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f124,f102,f57,f52,f47,f120])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    spl3_2 <=> k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    spl3_5 <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    r1_tarski(sK1,sK2) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.22/0.48    inference(subsumption_resolution,[],[f116,f59])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    r1_tarski(sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (~spl3_2 | ~spl3_3 | ~spl3_5)),
% 0.22/0.48    inference(resolution,[],[f104,f93])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_xboole_0(X0,k3_subset_1(sK0,sK1)) | r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | (~spl3_2 | ~spl3_3)),
% 0.22/0.48    inference(subsumption_resolution,[],[f92,f54])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_xboole_0(X0,k3_subset_1(sK0,sK1)) | r1_tarski(X0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl3_2),
% 0.22/0.48    inference(superposition,[],[f32,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) | ~spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f47])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    r1_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~spl3_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f102])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    spl3_6 | ~spl3_2 | ~spl3_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f106,f52,f47,f108])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    r1_xboole_0(sK2,k3_subset_1(sK0,sK1)) | (~spl3_2 | ~spl3_3)),
% 0.22/0.48    inference(forward_demodulation,[],[f94,f49])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    r1_xboole_0(sK2,k3_subset_1(sK0,sK2)) | ~spl3_3),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f63,f54,f54,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f61,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.48    inference(superposition,[],[f29,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.48    inference(rectify,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    spl3_5 | ~spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f95,f57,f102])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    r1_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~spl3_4),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f63,f59,f59,f33])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f24,f57])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    (sK1 != sK2 & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f17,f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : (X1 != X2 & k3_subset_1(X0,X2) = k3_subset_1(X0,X1) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK1 != X2 & k3_subset_1(sK0,X2) = k3_subset_1(sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X2] : (sK1 != X2 & k3_subset_1(sK0,X2) = k3_subset_1(sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (sK1 != sK2 & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : (X1 != X2 & k3_subset_1(X0,X2) = k3_subset_1(X0,X1) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : ((X1 != X2 & k3_subset_1(X0,X2) = k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (k3_subset_1(X0,X2) = k3_subset_1(X0,X1) => X1 = X2)))),
% 0.22/0.48    inference(negated_conjecture,[],[f8])).
% 0.22/0.48  fof(f8,conjecture,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (k3_subset_1(X0,X2) = k3_subset_1(X0,X1) => X1 = X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_subset_1)).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    spl3_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f25,f52])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f26,f47])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ~spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f27,f42])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    sK1 != sK2),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (13917)------------------------------
% 0.22/0.48  % (13917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (13917)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (13917)Memory used [KB]: 10618
% 0.22/0.48  % (13917)Time elapsed: 0.087 s
% 0.22/0.48  % (13917)------------------------------
% 0.22/0.48  % (13917)------------------------------
% 0.22/0.48  % (13911)Refutation not found, incomplete strategy% (13911)------------------------------
% 0.22/0.48  % (13911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (13911)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (13911)Memory used [KB]: 6140
% 0.22/0.48  % (13911)Time elapsed: 0.063 s
% 0.22/0.48  % (13911)------------------------------
% 0.22/0.48  % (13911)------------------------------
% 0.22/0.48  % (13900)Success in time 0.122 s
%------------------------------------------------------------------------------
