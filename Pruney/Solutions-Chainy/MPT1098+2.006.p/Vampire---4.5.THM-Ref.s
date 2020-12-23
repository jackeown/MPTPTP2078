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
% DateTime   : Thu Dec  3 13:08:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  84 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :   13
%              Number of atoms          :  111 ( 283 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f848,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f818,f843,f847])).

fof(f847,plain,(
    spl5_16 ),
    inference(avatar_contradiction_clause,[],[f846])).

fof(f846,plain,
    ( $false
    | spl5_16 ),
    inference(subsumption_resolution,[],[f845,f13])).

fof(f13,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
          | ~ r1_tarski(X3,X1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(X0,k2_zfmisc_1(X1,X2))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ! [X3] :
              ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
                & r1_tarski(X3,X1)
                & v1_finset_1(X3) )
          & r1_tarski(X0,k2_zfmisc_1(X1,X2))
          & v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ! [X3] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).

fof(f845,plain,
    ( ~ v1_finset_1(sK0)
    | spl5_16 ),
    inference(subsumption_resolution,[],[f844,f14])).

fof(f14,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f844,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ v1_finset_1(sK0)
    | spl5_16 ),
    inference(resolution,[],[f817,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK3(X0,X1,X2),X1)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] :
          ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
          & r1_tarski(X4,X2)
          & v1_finset_1(X4)
          & r1_tarski(X3,X1)
          & v1_finset_1(X3) )
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X4))
              & r1_tarski(X4,X2)
              & v1_finset_1(X4)
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).

fof(f817,plain,
    ( ~ r1_tarski(sK3(sK0,sK1,sK2),sK1)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f815])).

fof(f815,plain,
    ( spl5_16
  <=> r1_tarski(sK3(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f843,plain,(
    spl5_15 ),
    inference(avatar_contradiction_clause,[],[f842])).

fof(f842,plain,
    ( $false
    | spl5_15 ),
    inference(subsumption_resolution,[],[f841,f13])).

fof(f841,plain,
    ( ~ v1_finset_1(sK0)
    | spl5_15 ),
    inference(subsumption_resolution,[],[f840,f14])).

fof(f840,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ v1_finset_1(sK0)
    | spl5_15 ),
    inference(resolution,[],[f813,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( v1_finset_1(sK3(X0,X1,X2))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f813,plain,
    ( ~ v1_finset_1(sK3(sK0,sK1,sK2))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f811])).

fof(f811,plain,
    ( spl5_15
  <=> v1_finset_1(sK3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f818,plain,
    ( ~ spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f802,f815,f811])).

fof(f802,plain,
    ( ~ r1_tarski(sK3(sK0,sK1,sK2),sK1)
    | ~ v1_finset_1(sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f800,f12])).

fof(f12,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
      | ~ r1_tarski(X3,sK1)
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f800,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK2)) ),
    inference(subsumption_resolution,[],[f799,f13])).

fof(f799,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK2))
    | ~ v1_finset_1(sK0) ),
    inference(subsumption_resolution,[],[f793,f14])).

fof(f793,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK2))
    | ~ r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ v1_finset_1(sK0) ),
    inference(resolution,[],[f772,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2)))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f772,plain,(
    ! [X8,X7] :
      ( ~ r1_tarski(X7,k2_zfmisc_1(X8,sK4(sK0,sK1,sK2)))
      | r1_tarski(X7,k2_zfmisc_1(X8,sK2)) ) ),
    inference(superposition,[],[f117,f761])).

fof(f761,plain,(
    sK2 = k2_xboole_0(sK2,sK4(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f754,f13])).

fof(f754,plain,
    ( sK2 = k2_xboole_0(sK2,sK4(sK0,sK1,sK2))
    | ~ v1_finset_1(sK0) ),
    inference(resolution,[],[f171,f14])).

fof(f171,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(X5,X6))
      | k2_xboole_0(X6,sK4(X4,X5,X6)) = X6
      | ~ v1_finset_1(X4) ) ),
    inference(forward_demodulation,[],[f156,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f156,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(X5,X6))
      | ~ v1_finset_1(X4)
      | k2_xboole_0(sK4(X4,X5,X6),X6) = X6 ) ),
    inference(resolution,[],[f23,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK4(X0,X1,X2),X2)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f117,plain,(
    ! [X14,X12,X15,X13] :
      ( r1_tarski(X15,k2_zfmisc_1(X12,k2_xboole_0(X13,X14)))
      | ~ r1_tarski(X15,k2_zfmisc_1(X12,X14)) ) ),
    inference(superposition,[],[f19,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.36  % Computer   : n008.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % WCLimit    : 600
% 0.13/0.36  % DateTime   : Tue Dec  1 10:29:30 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.45  % (17494)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.45  % (17493)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.45  % (17491)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.45  % (17492)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.50  % (17490)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.50  % (17487)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.51  % (17489)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.51  % (17498)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.51  % (17496)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.51  % (17495)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.51  % (17497)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.52  % (17488)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.56  % (17487)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f848,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f818,f843,f847])).
% 0.22/0.56  fof(f847,plain,(
% 0.22/0.56    spl5_16),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f846])).
% 0.22/0.56  fof(f846,plain,(
% 0.22/0.56    $false | spl5_16),
% 0.22/0.56    inference(subsumption_resolution,[],[f845,f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    v1_finset_1(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.22/0.56    inference(negated_conjecture,[],[f6])).
% 0.22/0.56  fof(f6,conjecture,(
% 0.22/0.56    ! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).
% 0.22/0.56  fof(f845,plain,(
% 0.22/0.56    ~v1_finset_1(sK0) | spl5_16),
% 0.22/0.56    inference(subsumption_resolution,[],[f844,f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f844,plain,(
% 0.22/0.56    ~r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) | ~v1_finset_1(sK0) | spl5_16),
% 0.22/0.56    inference(resolution,[],[f817,f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r1_tarski(sK3(X0,X1,X2),X1) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ~(! [X3,X4] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).
% 0.22/0.56  fof(f817,plain,(
% 0.22/0.56    ~r1_tarski(sK3(sK0,sK1,sK2),sK1) | spl5_16),
% 0.22/0.56    inference(avatar_component_clause,[],[f815])).
% 0.22/0.56  fof(f815,plain,(
% 0.22/0.56    spl5_16 <=> r1_tarski(sK3(sK0,sK1,sK2),sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.56  fof(f843,plain,(
% 0.22/0.56    spl5_15),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f842])).
% 0.22/0.56  fof(f842,plain,(
% 0.22/0.56    $false | spl5_15),
% 0.22/0.56    inference(subsumption_resolution,[],[f841,f13])).
% 0.22/0.56  fof(f841,plain,(
% 0.22/0.56    ~v1_finset_1(sK0) | spl5_15),
% 0.22/0.56    inference(subsumption_resolution,[],[f840,f14])).
% 0.22/0.56  fof(f840,plain,(
% 0.22/0.56    ~r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) | ~v1_finset_1(sK0) | spl5_15),
% 0.22/0.56    inference(resolution,[],[f813,f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (v1_finset_1(sK3(X0,X1,X2)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f813,plain,(
% 0.22/0.56    ~v1_finset_1(sK3(sK0,sK1,sK2)) | spl5_15),
% 0.22/0.56    inference(avatar_component_clause,[],[f811])).
% 0.22/0.56  fof(f811,plain,(
% 0.22/0.56    spl5_15 <=> v1_finset_1(sK3(sK0,sK1,sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.56  fof(f818,plain,(
% 0.22/0.56    ~spl5_15 | ~spl5_16),
% 0.22/0.56    inference(avatar_split_clause,[],[f802,f815,f811])).
% 0.22/0.56  fof(f802,plain,(
% 0.22/0.56    ~r1_tarski(sK3(sK0,sK1,sK2),sK1) | ~v1_finset_1(sK3(sK0,sK1,sK2))),
% 0.22/0.56    inference(resolution,[],[f800,f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ( ! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f800,plain,(
% 0.22/0.56    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f799,f13])).
% 0.22/0.56  fof(f799,plain,(
% 0.22/0.56    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK2)) | ~v1_finset_1(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f793,f14])).
% 0.22/0.56  fof(f793,plain,(
% 0.22/0.56    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK2)) | ~r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) | ~v1_finset_1(sK0)),
% 0.22/0.56    inference(resolution,[],[f772,f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2))) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f772,plain,(
% 0.22/0.56    ( ! [X8,X7] : (~r1_tarski(X7,k2_zfmisc_1(X8,sK4(sK0,sK1,sK2))) | r1_tarski(X7,k2_zfmisc_1(X8,sK2))) )),
% 0.22/0.56    inference(superposition,[],[f117,f761])).
% 0.22/0.56  fof(f761,plain,(
% 0.22/0.56    sK2 = k2_xboole_0(sK2,sK4(sK0,sK1,sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f754,f13])).
% 0.22/0.56  fof(f754,plain,(
% 0.22/0.56    sK2 = k2_xboole_0(sK2,sK4(sK0,sK1,sK2)) | ~v1_finset_1(sK0)),
% 0.22/0.56    inference(resolution,[],[f171,f14])).
% 0.22/0.56  fof(f171,plain,(
% 0.22/0.56    ( ! [X6,X4,X5] : (~r1_tarski(X4,k2_zfmisc_1(X5,X6)) | k2_xboole_0(X6,sK4(X4,X5,X6)) = X6 | ~v1_finset_1(X4)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f156,f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.56  fof(f156,plain,(
% 0.22/0.56    ( ! [X6,X4,X5] : (~r1_tarski(X4,k2_zfmisc_1(X5,X6)) | ~v1_finset_1(X4) | k2_xboole_0(sK4(X4,X5,X6),X6) = X6) )),
% 0.22/0.56    inference(resolution,[],[f23,f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,plain,(
% 0.22/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r1_tarski(sK4(X0,X1,X2),X2) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    ( ! [X14,X12,X15,X13] : (r1_tarski(X15,k2_zfmisc_1(X12,k2_xboole_0(X13,X14))) | ~r1_tarski(X15,k2_zfmisc_1(X12,X14))) )),
% 0.22/0.56    inference(superposition,[],[f19,f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (17487)------------------------------
% 0.22/0.56  % (17487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (17487)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (17487)Memory used [KB]: 11641
% 0.22/0.56  % (17487)Time elapsed: 0.118 s
% 0.22/0.56  % (17487)------------------------------
% 0.22/0.56  % (17487)------------------------------
% 0.22/0.56  % (17486)Success in time 0.187 s
%------------------------------------------------------------------------------
