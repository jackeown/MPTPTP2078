%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  95 expanded)
%              Number of leaves         :   12 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  140 ( 267 expanded)
%              Number of equality atoms :   42 (  84 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f63,f89,f102,f111])).

fof(f111,plain,
    ( ~ spl3_8
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | ~ spl3_8
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f88,f101,f106])).

fof(f106,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k8_relset_1(k1_xboole_0,X5,X4,X6) ) ),
    inference(forward_demodulation,[],[f105,f35])).

fof(f35,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f105,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | k1_xboole_0 = k8_relset_1(k1_xboole_0,X5,X4,X6) ) ),
    inference(resolution,[],[f103,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f25,f22])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k8_relset_1(X1,X2,X0,X3),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f31,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f101,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_10
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f88,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_8
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f102,plain,
    ( ~ spl3_10
    | spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f71,f60,f53,f99])).

fof(f53,plain,
    ( spl3_4
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f60,plain,
    ( spl3_5
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f71,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)
    | spl3_4
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f55,f67])).

fof(f67,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f66,f22])).

fof(f66,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2
    | ~ spl3_5 ),
    inference(resolution,[],[f62,f25])).

fof(f62,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f55,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f89,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f72,f60,f48,f86])).

fof(f48,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f72,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f50,f67])).

fof(f50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f63,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f57,f48,f60])).

fof(f57,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_3 ),
    inference(resolution,[],[f26,f50])).

fof(f56,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f21,f53])).

fof(f21,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_2(sK2,k1_xboole_0,sK0)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_2(sK2,k1_xboole_0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_2(X2,k1_xboole_0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(f51,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f46,f48])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f20,f35])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:52:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (11657)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.46  % (11650)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.48  % (11650)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f51,f56,f63,f89,f102,f111])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    ~spl3_8 | spl3_10),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f107])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    $false | (~spl3_8 | spl3_10)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f88,f101,f106])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X5,X4,X6)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f105,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X5,X4,X6)) )),
% 0.20/0.48    inference(resolution,[],[f103,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(resolution,[],[f25,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (r1_tarski(k8_relset_1(X1,X2,X0,X3),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.48    inference(resolution,[],[f31,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.48    inference(nnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | spl3_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f99])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    spl3_10 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl3_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f86])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    spl3_8 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    ~spl3_10 | spl3_4 | ~spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f71,f60,f53,f99])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    spl3_4 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    spl3_5 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,k1_xboole_0,sK1) | (spl3_4 | ~spl3_5)),
% 0.20/0.48    inference(backward_demodulation,[],[f55,f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | ~spl3_5),
% 0.20/0.48    inference(subsumption_resolution,[],[f66,f22])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ~r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK2 | ~spl3_5),
% 0.20/0.48    inference(resolution,[],[f62,f25])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    r1_tarski(sK2,k1_xboole_0) | ~spl3_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f60])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl3_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f53])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    spl3_8 | ~spl3_3 | ~spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f72,f60,f48,f86])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl3_3 | ~spl3_5)),
% 0.20/0.48    inference(backward_demodulation,[],[f50,f67])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f48])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl3_5 | ~spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f57,f48,f60])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    r1_tarski(sK2,k1_xboole_0) | ~spl3_3),
% 0.20/0.48    inference(resolution,[],[f26,f50])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ~spl3_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f21,f53])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_2(sK2,k1_xboole_0,sK0) & v1_funct_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.48    inference(negated_conjecture,[],[f6])).
% 0.20/0.48  fof(f6,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f46,f48])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.48    inference(forward_demodulation,[],[f20,f35])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (11650)------------------------------
% 0.20/0.48  % (11650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (11650)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (11650)Memory used [KB]: 6140
% 0.20/0.48  % (11650)Time elapsed: 0.081 s
% 0.20/0.48  % (11650)------------------------------
% 0.20/0.48  % (11650)------------------------------
% 0.20/0.48  % (11647)Success in time 0.125 s
%------------------------------------------------------------------------------
