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
% DateTime   : Thu Dec  3 13:08:27 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   41 (  78 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 ( 270 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f846,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f390,f845])).

fof(f845,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f844,f327])).

fof(f327,plain,
    ( spl5_3
  <=> v1_finset_1(sK3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f844,plain,(
    ~ v1_finset_1(sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f843,f51])).

fof(f51,plain,(
    r1_tarski(sK3(sK0,sK1,sK2),sK1) ),
    inference(resolution,[],[f40,f14])).

fof(f14,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
          | ~ r1_tarski(X3,X1)
          | ~ v1_finset_1(X3) )
      & r1_tarski(X0,k2_zfmisc_1(X1,X2))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ! [X3] :
              ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
                & r1_tarski(X3,X1)
                & v1_finset_1(X3) )
          & r1_tarski(X0,k2_zfmisc_1(X1,X2))
          & v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ! [X3] :
            ~ ( r1_tarski(X0,k2_zfmisc_1(X3,X2))
              & r1_tarski(X3,X1)
              & v1_finset_1(X3) )
        & r1_tarski(X0,k2_zfmisc_1(X1,X2))
        & v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
      | r1_tarski(sK3(sK0,X0,X1),X0) ) ),
    inference(resolution,[],[f20,f13])).

fof(f13,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_finset_1(X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | r1_tarski(sK3(X0,X1,X2),X1) ) ),
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f843,plain,
    ( ~ r1_tarski(sK3(sK0,sK1,sK2),sK1)
    | ~ v1_finset_1(sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f824,f55])).

fof(f55,plain,(
    r1_tarski(sK4(sK0,sK1,sK2),sK2) ),
    inference(resolution,[],[f45,f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
      | r1_tarski(sK4(sK0,X0,X1),X1) ) ),
    inference(resolution,[],[f22,f13])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_finset_1(X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | r1_tarski(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f824,plain,
    ( ~ r1_tarski(sK4(sK0,sK1,sK2),sK2)
    | ~ r1_tarski(sK3(sK0,sK1,sK2),sK1)
    | ~ v1_finset_1(sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f282,f12])).

fof(f12,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK0,k2_zfmisc_1(X3,sK2))
      | ~ r1_tarski(X3,sK1)
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f282,plain,(
    ! [X3] :
      ( r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),X3))
      | ~ r1_tarski(sK4(sK0,sK1,sK2),X3) ) ),
    inference(resolution,[],[f278,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f278,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),X0)
      | r1_tarski(sK0,X0) ) ),
    inference(superposition,[],[f18,f101])).

fof(f101,plain,(
    k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)) = k2_xboole_0(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))) ),
    inference(resolution,[],[f75,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f75,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2))) ),
    inference(resolution,[],[f48,f14])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,k2_zfmisc_1(X0,X1))
      | r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,X0,X1),sK4(sK0,X0,X1))) ) ),
    inference(resolution,[],[f23,f13])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_finset_1(X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f390,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f388,f13])).

fof(f388,plain,
    ( ~ v1_finset_1(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f387,f14])).

fof(f387,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ v1_finset_1(sK0)
    | spl5_3 ),
    inference(resolution,[],[f328,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( v1_finset_1(sK3(X0,X1,X2))
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f328,plain,
    ( ~ v1_finset_1(sK3(sK0,sK1,sK2))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.41  % (2215)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.19/0.45  % (2212)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.19/0.45  % (2221)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.19/0.45  % (2213)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.19/0.46  % (2219)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.19/0.47  % (2216)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.19/0.49  % (2209)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.19/0.50  % (2218)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.19/0.51  % (2212)Refutation found. Thanks to Tanya!
% 0.19/0.51  % SZS status Theorem for theBenchmark
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f846,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f390,f845])).
% 0.19/0.51  fof(f845,plain,(
% 0.19/0.51    ~spl5_3),
% 0.19/0.51    inference(avatar_split_clause,[],[f844,f327])).
% 0.19/0.51  fof(f327,plain,(
% 0.19/0.51    spl5_3 <=> v1_finset_1(sK3(sK0,sK1,sK2))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.51  fof(f844,plain,(
% 0.19/0.51    ~v1_finset_1(sK3(sK0,sK1,sK2))),
% 0.19/0.51    inference(subsumption_resolution,[],[f843,f51])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    r1_tarski(sK3(sK0,sK1,sK2),sK1)),
% 0.19/0.51    inference(resolution,[],[f40,f14])).
% 0.19/0.51  fof(f14,plain,(
% 0.19/0.51    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.19/0.51    inference(cnf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,plain,(
% 0.19/0.51    ? [X0,X1,X2] : (! [X3] : (~r1_tarski(X0,k2_zfmisc_1(X3,X2)) | ~r1_tarski(X3,X1) | ~v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,negated_conjecture,(
% 0.19/0.51    ~! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.19/0.51    inference(negated_conjecture,[],[f5])).
% 0.19/0.51  fof(f5,conjecture,(
% 0.19/0.51    ! [X0,X1,X2] : ~(! [X3] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X2)) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_finset_1)).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tarski(sK0,k2_zfmisc_1(X0,X1)) | r1_tarski(sK3(sK0,X0,X1),X0)) )),
% 0.19/0.51    inference(resolution,[],[f20,f13])).
% 0.19/0.51  fof(f13,plain,(
% 0.19/0.51    v1_finset_1(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f7])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~v1_finset_1(X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | r1_tarski(sK3(X0,X1,X2),X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (? [X3,X4] : (r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : ~(! [X3,X4] : ~(r1_tarski(X0,k2_zfmisc_1(X3,X4)) & r1_tarski(X4,X2) & v1_finset_1(X4) & r1_tarski(X3,X1) & v1_finset_1(X3)) & r1_tarski(X0,k2_zfmisc_1(X1,X2)) & v1_finset_1(X0))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_finset_1)).
% 0.19/0.51  fof(f843,plain,(
% 0.19/0.51    ~r1_tarski(sK3(sK0,sK1,sK2),sK1) | ~v1_finset_1(sK3(sK0,sK1,sK2))),
% 0.19/0.51    inference(subsumption_resolution,[],[f824,f55])).
% 0.19/0.51  fof(f55,plain,(
% 0.19/0.51    r1_tarski(sK4(sK0,sK1,sK2),sK2)),
% 0.19/0.51    inference(resolution,[],[f45,f14])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tarski(sK0,k2_zfmisc_1(X0,X1)) | r1_tarski(sK4(sK0,X0,X1),X1)) )),
% 0.19/0.51    inference(resolution,[],[f22,f13])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~v1_finset_1(X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | r1_tarski(sK4(X0,X1,X2),X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f11])).
% 0.19/0.51  fof(f824,plain,(
% 0.19/0.51    ~r1_tarski(sK4(sK0,sK1,sK2),sK2) | ~r1_tarski(sK3(sK0,sK1,sK2),sK1) | ~v1_finset_1(sK3(sK0,sK1,sK2))),
% 0.19/0.51    inference(resolution,[],[f282,f12])).
% 0.19/0.51  fof(f12,plain,(
% 0.19/0.51    ( ! [X3] : (~r1_tarski(sK0,k2_zfmisc_1(X3,sK2)) | ~r1_tarski(X3,sK1) | ~v1_finset_1(X3)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f7])).
% 0.19/0.51  fof(f282,plain,(
% 0.19/0.51    ( ! [X3] : (r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),X3)) | ~r1_tarski(sK4(sK0,sK1,sK2),X3)) )),
% 0.19/0.51    inference(resolution,[],[f278,f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,plain,(
% 0.19/0.51    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.19/0.51  fof(f278,plain,(
% 0.19/0.51    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),X0) | r1_tarski(sK0,X0)) )),
% 0.19/0.51    inference(superposition,[],[f18,f101])).
% 0.19/0.51  fof(f101,plain,(
% 0.19/0.51    k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)) = k2_xboole_0(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))),
% 0.19/0.51    inference(resolution,[],[f75,f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.19/0.51    inference(cnf_transformation,[],[f8])).
% 0.19/0.51  fof(f8,plain,(
% 0.19/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.51    inference(ennf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.51  fof(f75,plain,(
% 0.19/0.51    r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)))),
% 0.19/0.51    inference(resolution,[],[f48,f14])).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~r1_tarski(sK0,k2_zfmisc_1(X0,X1)) | r1_tarski(sK0,k2_zfmisc_1(sK3(sK0,X0,X1),sK4(sK0,X0,X1)))) )),
% 0.19/0.51    inference(resolution,[],[f23,f13])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~v1_finset_1(X0) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | r1_tarski(X0,k2_zfmisc_1(sK3(X0,X1,X2),sK4(X0,X1,X2)))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f11])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f10])).
% 0.19/0.51  fof(f10,plain,(
% 0.19/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.19/0.51    inference(ennf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.19/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.19/0.51  fof(f390,plain,(
% 0.19/0.51    spl5_3),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f389])).
% 0.19/0.51  fof(f389,plain,(
% 0.19/0.51    $false | spl5_3),
% 0.19/0.51    inference(subsumption_resolution,[],[f388,f13])).
% 0.19/0.51  fof(f388,plain,(
% 0.19/0.51    ~v1_finset_1(sK0) | spl5_3),
% 0.19/0.51    inference(subsumption_resolution,[],[f387,f14])).
% 0.19/0.51  fof(f387,plain,(
% 0.19/0.51    ~r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) | ~v1_finset_1(sK0) | spl5_3),
% 0.19/0.51    inference(resolution,[],[f328,f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (v1_finset_1(sK3(X0,X1,X2)) | ~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_finset_1(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f11])).
% 0.19/0.51  fof(f328,plain,(
% 0.19/0.51    ~v1_finset_1(sK3(sK0,sK1,sK2)) | spl5_3),
% 0.19/0.51    inference(avatar_component_clause,[],[f327])).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (2212)------------------------------
% 0.19/0.51  % (2212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (2212)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (2212)Memory used [KB]: 12153
% 0.19/0.51  % (2212)Time elapsed: 0.059 s
% 0.19/0.51  % (2212)------------------------------
% 0.19/0.51  % (2212)------------------------------
% 0.19/0.51  % (2198)Success in time 0.155 s
%------------------------------------------------------------------------------
