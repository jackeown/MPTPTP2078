%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 217 expanded)
%              Number of leaves         :   14 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  170 ( 841 expanded)
%              Number of equality atoms :   24 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f51,f63,f192])).

fof(f192,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f191])).

% (31897)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% (31906)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f191,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f190,f64])).

fof(f64,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | spl3_2 ),
    inference(forward_demodulation,[],[f48,f57])).

fof(f57,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | ~ r1_xboole_0(sK1,sK2) )
    & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | r1_xboole_0(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | r1_xboole_0(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
            | ~ r1_xboole_0(sK1,X2) )
          & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
            | r1_xboole_0(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
          | ~ r1_xboole_0(sK1,X2) )
        & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
          | r1_xboole_0(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | ~ r1_xboole_0(sK1,sK2) )
      & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | r1_xboole_0(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,X2)
          <~> r1_tarski(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,X2)
            <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f48,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl3_2
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f190,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f187,f132])).

fof(f132,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f131,f101])).

fof(f101,plain,(
    ! [X1] : r1_tarski(sK1,k2_xboole_0(sK0,X1)) ),
    inference(superposition,[],[f41,f85])).

fof(f85,plain,(
    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f67,f84])).

fof(f84,plain,(
    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f77,f56])).

fof(f56,plain,(
    k4_xboole_0(sK0,sK1) = k3_subset_1(sK0,sK1) ),
    inference(resolution,[],[f34,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f35,f25])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f67,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f66,f34])).

fof(f66,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f65,f25])).

fof(f65,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f33,f56])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f41,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f36,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f36,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f131,plain,
    ( ! [X6] :
        ( ~ r1_tarski(sK1,k2_xboole_0(X6,sK2))
        | r1_tarski(sK1,X6) )
    | ~ spl3_1 ),
    inference(resolution,[],[f39,f45])).

fof(f45,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_1
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f187,plain,
    ( ~ r1_tarski(sK1,sK0)
    | r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_1 ),
    inference(superposition,[],[f133,f176])).

fof(f176,plain,(
    sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f40,f89])).

fof(f89,plain,(
    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f70,f88])).

fof(f88,plain,(
    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f78,f57])).

fof(f78,plain,(
    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f35,f26])).

fof(f70,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f69,f34])).

fof(f69,plain,(
    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f68,f26])).

fof(f68,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f33,f57])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k2_xboole_0(sK2,X0))
        | r1_tarski(sK1,X0) )
    | ~ spl3_1 ),
    inference(superposition,[],[f131,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f63,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f60,f44])).

fof(f44,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f60,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f59,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f59,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f49,f57])).

fof(f49,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f51,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f28,f47,f43])).

fof(f28,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f27,f47,f43])).

fof(f27,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:10:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (31905)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (31909)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (31898)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (31904)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (31901)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (31909)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f193,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f50,f51,f63,f192])).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    ~spl3_1 | spl3_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f191])).
% 0.21/0.47  % (31897)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (31906)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  fof(f191,plain,(
% 0.21/0.47    $false | (~spl3_1 | spl3_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f190,f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ~r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | spl3_2),
% 0.21/0.47    inference(forward_demodulation,[],[f48,f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.21/0.47    inference(resolution,[],[f34,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(nnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,X2) <~> r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f11])).
% 0.21/0.47  fof(f11,conjecture,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl3_2 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f187,f132])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    r1_tarski(sK1,sK0) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f131,f101])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ( ! [X1] : (r1_tarski(sK1,k2_xboole_0(sK0,X1))) )),
% 0.21/0.47    inference(superposition,[],[f41,f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(backward_demodulation,[],[f67,f84])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(forward_demodulation,[],[f77,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    k4_xboole_0(sK0,sK1) = k3_subset_1(sK0,sK1)),
% 0.21/0.47    inference(resolution,[],[f34,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.21/0.47    inference(resolution,[],[f35,f25])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(resolution,[],[f66,f34])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f65,f25])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(superposition,[],[f33,f56])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(X0,X2))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f36,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ( ! [X6] : (~r1_tarski(sK1,k2_xboole_0(X6,sK2)) | r1_tarski(sK1,X6)) ) | ~spl3_1),
% 0.21/0.47    inference(resolution,[],[f39,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    r1_xboole_0(sK1,sK2) | ~spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl3_1 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X2) | r1_tarski(X0,X1) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.21/0.47  fof(f187,plain,(
% 0.21/0.47    ~r1_tarski(sK1,sK0) | r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_1),
% 0.21/0.47    inference(superposition,[],[f133,f176])).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK2))),
% 0.21/0.47    inference(superposition,[],[f40,f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.21/0.47    inference(backward_demodulation,[],[f70,f88])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    sK2 = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 0.21/0.47    inference(forward_demodulation,[],[f78,f57])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 0.21/0.47    inference(resolution,[],[f35,f26])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK2))),
% 0.21/0.47    inference(resolution,[],[f69,f34])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f68,f26])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.47    inference(superposition,[],[f33,f57])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.47    inference(definition_unfolding,[],[f32,f31])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(sK1,k2_xboole_0(sK2,X0)) | r1_tarski(sK1,X0)) ) | ~spl3_1),
% 0.21/0.47    inference(superposition,[],[f131,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl3_1 | ~spl3_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    $false | (spl3_1 | ~spl3_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f60,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ~r1_xboole_0(sK1,sK2) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f43])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    r1_xboole_0(sK1,sK2) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f59,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | ~spl3_2),
% 0.21/0.47    inference(backward_demodulation,[],[f49,f57])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f47])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ~spl3_1 | ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f47,f43])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl3_1 | spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f47,f43])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (31909)------------------------------
% 0.21/0.47  % (31909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (31909)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (31909)Memory used [KB]: 6268
% 0.21/0.47  % (31909)Time elapsed: 0.010 s
% 0.21/0.47  % (31909)------------------------------
% 0.21/0.47  % (31909)------------------------------
% 0.21/0.47  % (31899)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (31906)Refutation not found, incomplete strategy% (31906)------------------------------
% 0.21/0.48  % (31906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31906)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31906)Memory used [KB]: 10746
% 0.21/0.48  % (31906)Time elapsed: 0.066 s
% 0.21/0.48  % (31906)------------------------------
% 0.21/0.48  % (31906)------------------------------
% 0.21/0.48  % (31894)Success in time 0.118 s
%------------------------------------------------------------------------------
