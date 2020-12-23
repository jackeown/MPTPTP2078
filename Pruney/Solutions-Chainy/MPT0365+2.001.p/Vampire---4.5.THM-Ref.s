%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:14 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 145 expanded)
%              Number of leaves         :    9 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  150 ( 478 expanded)
%              Number of equality atoms :   20 (  77 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f148,f192,f238])).

fof(f238,plain,(
    ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f236,f14])).

fof(f14,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
                & r1_xboole_0(X1,X2) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
              & r1_xboole_0(X1,X2) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

fof(f236,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f234,f133])).

fof(f133,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    inference(subsumption_resolution,[],[f132,f17])).

fof(f17,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f132,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | sK1 = k3_subset_1(sK0,sK2) ),
    inference(resolution,[],[f131,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f131,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f128,f15])).

fof(f15,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f128,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f124,f18])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f124,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r1_tarski(X0,k3_subset_1(sK0,sK2))
      | ~ r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f22,f14])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f234,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_5 ),
    inference(resolution,[],[f211,f93])).

fof(f93,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f92,f14])).

fof(f92,plain,
    ( r1_xboole_0(k3_subset_1(sK0,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f70,f30])).

fof(f30,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_subset_1(sK0,X0),k3_subset_1(sK0,sK2))
      | r1_xboole_0(k3_subset_1(sK0,X0),sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f65,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r1_tarski(X0,k3_subset_1(sK0,sK2))
      | r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f21,f14])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k3_subset_1(sK0,X0),sK2)
        | r1_tarski(k3_subset_1(sK0,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f187,f143])).

fof(f143,plain,
    ( sK2 = k3_subset_1(sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl3_5
  <=> sK2 = k3_subset_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f187,plain,(
    ! [X0] :
      ( r1_tarski(k3_subset_1(sK0,X0),sK1)
      | ~ r1_xboole_0(k3_subset_1(sK0,X0),k3_subset_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f179,f20])).

fof(f179,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r1_tarski(X1,sK1)
      | ~ r1_xboole_0(X1,k3_subset_1(sK0,sK1)) ) ),
    inference(resolution,[],[f24,f18])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2)
      | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

fof(f192,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f190,f18])).

fof(f190,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_6 ),
    inference(subsumption_resolution,[],[f189,f147])).

fof(f147,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl3_6
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f189,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f183,f16])).

fof(f16,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f183,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k3_subset_1(sK0,X0),k3_subset_1(sK0,sK2))
      | r1_tarski(k3_subset_1(sK0,X0),sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f178,f20])).

fof(f178,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r1_tarski(X0,sK2)
      | ~ r1_xboole_0(X0,k3_subset_1(sK0,sK2)) ) ),
    inference(resolution,[],[f24,f14])).

fof(f148,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f139,f145,f141])).

fof(f139,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | sK2 = k3_subset_1(sK0,sK1) ),
    inference(resolution,[],[f137,f27])).

fof(f137,plain,(
    r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f134,f45])).

fof(f45,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f42])).

fof(f42,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f32,f34])).

fof(f34,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f29,f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f28,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f134,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f125,f14])).

fof(f125,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r1_tarski(X1,k3_subset_1(sK0,sK1))
      | ~ r1_xboole_0(X1,sK1) ) ),
    inference(resolution,[],[f22,f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:05:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.46  % (16751)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.46  % (16743)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.47  % (16751)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % (16729)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f239,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f148,f192,f238])).
% 0.19/0.48  fof(f238,plain,(
% 0.19/0.48    ~spl3_5),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f237])).
% 0.19/0.48  fof(f237,plain,(
% 0.19/0.48    $false | ~spl3_5),
% 0.19/0.48    inference(subsumption_resolution,[],[f236,f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.48    inference(cnf_transformation,[],[f10])).
% 0.19/0.48  fof(f10,plain,(
% 0.19/0.48    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.48    inference(flattening,[],[f9])).
% 0.19/0.48  fof(f9,plain,(
% 0.19/0.48    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & (r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,negated_conjecture,(
% 0.19/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 0.19/0.48    inference(negated_conjecture,[],[f7])).
% 0.19/0.48  fof(f7,conjecture,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).
% 0.19/0.48  fof(f236,plain,(
% 0.19/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_5),
% 0.19/0.48    inference(subsumption_resolution,[],[f234,f133])).
% 0.19/0.48  fof(f133,plain,(
% 0.19/0.48    ~r1_tarski(k3_subset_1(sK0,sK2),sK1)),
% 0.19/0.48    inference(subsumption_resolution,[],[f132,f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    sK1 != k3_subset_1(sK0,sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f10])).
% 0.19/0.48  fof(f132,plain,(
% 0.19/0.48    ~r1_tarski(k3_subset_1(sK0,sK2),sK1) | sK1 = k3_subset_1(sK0,sK2)),
% 0.19/0.48    inference(resolution,[],[f131,f27])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.48  fof(f131,plain,(
% 0.19/0.48    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.19/0.48    inference(subsumption_resolution,[],[f128,f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    r1_xboole_0(sK1,sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f10])).
% 0.19/0.48  fof(f128,plain,(
% 0.19/0.48    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)),
% 0.19/0.48    inference(resolution,[],[f124,f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.48    inference(cnf_transformation,[],[f10])).
% 0.19/0.48  fof(f124,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(X0,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(X0,sK2)) )),
% 0.19/0.48    inference(resolution,[],[f22,f14])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 0.19/0.48  fof(f234,plain,(
% 0.19/0.48    r1_tarski(k3_subset_1(sK0,sK2),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_5),
% 0.19/0.48    inference(resolution,[],[f211,f93])).
% 0.19/0.48  fof(f93,plain,(
% 0.19/0.48    r1_xboole_0(k3_subset_1(sK0,sK2),sK2)),
% 0.19/0.48    inference(subsumption_resolution,[],[f92,f14])).
% 0.19/0.48  fof(f92,plain,(
% 0.19/0.48    r1_xboole_0(k3_subset_1(sK0,sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.48    inference(resolution,[],[f70,f30])).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.48    inference(equality_resolution,[],[f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f3])).
% 0.19/0.48  fof(f70,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(k3_subset_1(sK0,X0),k3_subset_1(sK0,sK2)) | r1_xboole_0(k3_subset_1(sK0,X0),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.19/0.48    inference(resolution,[],[f65,f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f11])).
% 0.19/0.48  fof(f11,plain,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.19/0.48  fof(f65,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r1_tarski(X0,k3_subset_1(sK0,sK2)) | r1_xboole_0(X0,sK2)) )),
% 0.19/0.48    inference(resolution,[],[f21,f14])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f12])).
% 0.19/0.48  fof(f211,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_xboole_0(k3_subset_1(sK0,X0),sK2) | r1_tarski(k3_subset_1(sK0,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl3_5),
% 0.19/0.48    inference(backward_demodulation,[],[f187,f143])).
% 0.19/0.48  fof(f143,plain,(
% 0.19/0.48    sK2 = k3_subset_1(sK0,sK1) | ~spl3_5),
% 0.19/0.48    inference(avatar_component_clause,[],[f141])).
% 0.19/0.48  fof(f141,plain,(
% 0.19/0.48    spl3_5 <=> sK2 = k3_subset_1(sK0,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.48  fof(f187,plain,(
% 0.19/0.48    ( ! [X0] : (r1_tarski(k3_subset_1(sK0,X0),sK1) | ~r1_xboole_0(k3_subset_1(sK0,X0),k3_subset_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.19/0.48    inference(resolution,[],[f179,f20])).
% 0.19/0.48  fof(f179,plain,(
% 0.19/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r1_tarski(X1,sK1) | ~r1_xboole_0(X1,k3_subset_1(sK0,sK1))) )),
% 0.19/0.48    inference(resolution,[],[f24,f18])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).
% 0.19/0.48  fof(f192,plain,(
% 0.19/0.48    spl3_6),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f191])).
% 0.19/0.48  fof(f191,plain,(
% 0.19/0.48    $false | spl3_6),
% 0.19/0.48    inference(subsumption_resolution,[],[f190,f18])).
% 0.19/0.48  fof(f190,plain,(
% 0.19/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_6),
% 0.19/0.48    inference(subsumption_resolution,[],[f189,f147])).
% 0.19/0.48  fof(f147,plain,(
% 0.19/0.48    ~r1_tarski(k3_subset_1(sK0,sK1),sK2) | spl3_6),
% 0.19/0.48    inference(avatar_component_clause,[],[f145])).
% 0.19/0.48  fof(f145,plain,(
% 0.19/0.48    spl3_6 <=> r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.48  fof(f189,plain,(
% 0.19/0.48    r1_tarski(k3_subset_1(sK0,sK1),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.48    inference(resolution,[],[f183,f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))),
% 0.19/0.48    inference(cnf_transformation,[],[f10])).
% 0.19/0.48  fof(f183,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_xboole_0(k3_subset_1(sK0,X0),k3_subset_1(sK0,sK2)) | r1_tarski(k3_subset_1(sK0,X0),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.19/0.48    inference(resolution,[],[f178,f20])).
% 0.19/0.48  fof(f178,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(X0,sK2) | ~r1_xboole_0(X0,k3_subset_1(sK0,sK2))) )),
% 0.19/0.48    inference(resolution,[],[f24,f14])).
% 0.19/0.48  fof(f148,plain,(
% 0.19/0.48    spl3_5 | ~spl3_6),
% 0.19/0.48    inference(avatar_split_clause,[],[f139,f145,f141])).
% 0.19/0.48  fof(f139,plain,(
% 0.19/0.48    ~r1_tarski(k3_subset_1(sK0,sK1),sK2) | sK2 = k3_subset_1(sK0,sK1)),
% 0.19/0.48    inference(resolution,[],[f137,f27])).
% 0.19/0.48  fof(f137,plain,(
% 0.19/0.48    r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 0.19/0.48    inference(subsumption_resolution,[],[f134,f45])).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    r1_xboole_0(sK2,sK1)),
% 0.19/0.48    inference(trivial_inequality_removal,[],[f42])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK2,sK1)),
% 0.19/0.48    inference(superposition,[],[f32,f34])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.19/0.48    inference(resolution,[],[f29,f15])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k3_xboole_0(X1,X0) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.19/0.48    inference(superposition,[],[f28,f19])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f2])).
% 0.19/0.48  fof(f134,plain,(
% 0.19/0.48    r1_tarski(sK2,k3_subset_1(sK0,sK1)) | ~r1_xboole_0(sK2,sK1)),
% 0.19/0.48    inference(resolution,[],[f125,f14])).
% 0.19/0.48  fof(f125,plain,(
% 0.19/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r1_tarski(X1,k3_subset_1(sK0,sK1)) | ~r1_xboole_0(X1,sK1)) )),
% 0.19/0.48    inference(resolution,[],[f22,f18])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (16751)------------------------------
% 0.19/0.48  % (16751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (16751)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (16751)Memory used [KB]: 10746
% 0.19/0.48  % (16751)Time elapsed: 0.061 s
% 0.19/0.48  % (16751)------------------------------
% 0.19/0.48  % (16751)------------------------------
% 0.19/0.48  % (16722)Success in time 0.134 s
%------------------------------------------------------------------------------
