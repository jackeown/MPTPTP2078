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
% DateTime   : Thu Dec  3 12:51:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 141 expanded)
%              Number of leaves         :   24 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  221 ( 344 expanded)
%              Number of equality atoms :   40 (  73 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f53,f57,f66,f72,f81,f88,f92,f124,f146,f153,f163,f169,f178])).

fof(f178,plain,
    ( ~ spl3_11
    | spl3_16
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl3_11
    | spl3_16
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f141,f173])).

fof(f173,plain,
    ( ! [X1] : v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X1)))
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(superposition,[],[f91,f168])).

fof(f168,plain,
    ( ! [X0] : k4_xboole_0(sK2,k7_relat_1(sK2,X0)) = k7_relat_1(sK2,k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(sK2))),X0))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl3_19
  <=> ! [X0] : k4_xboole_0(sK2,k7_relat_1(sK2,X0)) = k7_relat_1(sK2,k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(sK2))),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f91,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_11
  <=> ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f141,plain,
    ( ~ v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_16
  <=> v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f169,plain,
    ( spl3_19
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f93,f86,f51,f36,f167])).

fof(f36,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f51,plain,
    ( spl3_4
  <=> ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f86,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1))
        | ~ r1_tarski(k1_relat_1(X2),X0)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f93,plain,
    ( ! [X0] : k4_xboole_0(sK2,k7_relat_1(sK2,X0)) = k7_relat_1(sK2,k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(sK2))),X0))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f38,f52,f87])).

fof(f87,plain,
    ( ! [X2,X0,X1] :
        ( k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1))
        | ~ r1_tarski(k1_relat_1(X2),X0)
        | ~ v1_relat_1(X2) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f52,plain,
    ( ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f38,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f163,plain,
    ( ~ spl3_2
    | ~ spl3_7
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_7
    | spl3_18 ),
    inference(subsumption_resolution,[],[f43,f155])).

fof(f155,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl3_7
    | spl3_18 ),
    inference(unit_resulting_resolution,[],[f152,f65])).

fof(f65,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f152,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_18
  <=> r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f43,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f153,plain,
    ( ~ spl3_18
    | ~ spl3_13
    | spl3_17 ),
    inference(avatar_split_clause,[],[f147,f143,f122,f150])).

fof(f122,plain,
    ( spl3_13
  <=> ! [X0] : k4_xboole_0(k1_relat_1(sK2),X0) = k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f143,plain,
    ( spl3_17
  <=> r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f147,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1))
    | ~ spl3_13
    | spl3_17 ),
    inference(forward_demodulation,[],[f145,f123])).

fof(f123,plain,
    ( ! [X0] : k4_xboole_0(k1_relat_1(sK2),X0) = k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f145,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f143])).

fof(f146,plain,
    ( ~ spl3_16
    | ~ spl3_17
    | spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f77,f70,f46,f143,f139])).

fof(f46,plain,
    ( spl3_3
  <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f70,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k7_relat_1(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f77,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))))
    | ~ v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))
    | spl3_3
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))))
    | ~ v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))
    | spl3_3
    | ~ spl3_8 ),
    inference(superposition,[],[f48,f71])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X1,k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f48,plain,
    ( k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f124,plain,
    ( spl3_13
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f82,f79,f36,f122])).

fof(f79,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k4_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0)))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

% (17393)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f82,plain,
    ( ! [X0] : k4_xboole_0(k1_relat_1(sK2),X0) = k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)))
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f38,f80])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0)))
        | ~ v1_relat_1(X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f79])).

fof(f92,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f62,f55,f36,f90])).

% (17396)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f55,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f62,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f38,f56])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f88,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f34,f86])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f33,f25])).

fof(f25,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(forward_demodulation,[],[f28,f25])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

fof(f81,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f32,f79])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f31,f25])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f27,f25])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

fof(f72,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f24,f70])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,X1) = k1_xboole_0
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f66,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f57,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f53,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f23,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f49,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f30,f46])).

fof(f30,plain,(
    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(forward_demodulation,[],[f22,f25])).

fof(f22,plain,(
    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

fof(f44,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:44:21 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.20/0.48  % (17401)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (17392)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (17389)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % (17387)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (17388)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.50  % (17389)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (17395)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.51  % (17397)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f39,f44,f49,f53,f57,f66,f72,f81,f88,f92,f124,f146,f153,f163,f169,f178])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    ~spl3_11 | spl3_16 | ~spl3_19),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f177])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    $false | (~spl3_11 | spl3_16 | ~spl3_19)),
% 0.20/0.51    inference(subsumption_resolution,[],[f141,f173])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    ( ! [X1] : (v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X1)))) ) | (~spl3_11 | ~spl3_19)),
% 0.20/0.51    inference(superposition,[],[f91,f168])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(sK2,k7_relat_1(sK2,X0)) = k7_relat_1(sK2,k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(sK2))),X0))) ) | ~spl3_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f167])).
% 0.20/0.51  fof(f167,plain,(
% 0.20/0.51    spl3_19 <=> ! [X0] : k4_xboole_0(sK2,k7_relat_1(sK2,X0)) = k7_relat_1(sK2,k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(sK2))),X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) ) | ~spl3_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    spl3_11 <=> ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    ~v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))) | spl3_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f139])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    spl3_16 <=> v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    spl3_19 | ~spl3_1 | ~spl3_4 | ~spl3_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f93,f86,f51,f36,f167])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    spl3_1 <=> v1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    spl3_4 <=> ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl3_10 <=> ! [X1,X0,X2] : (k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(sK2,k7_relat_1(sK2,X0)) = k7_relat_1(sK2,k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(sK2))),X0))) ) | (~spl3_1 | ~spl3_4 | ~spl3_10)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f38,f52,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) ) | ~spl3_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f86])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) ) | ~spl3_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f51])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    v1_relat_1(sK2) | ~spl3_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f36])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    ~spl3_2 | ~spl3_7 | spl3_18),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f162])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    $false | (~spl3_2 | ~spl3_7 | spl3_18)),
% 0.20/0.51    inference(subsumption_resolution,[],[f43,f155])).
% 0.20/0.51  fof(f155,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK1) | (~spl3_7 | spl3_18)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f152,f65])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) ) | ~spl3_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    spl3_7 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.51  fof(f152,plain,(
% 0.20/0.51    ~r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1)) | spl3_18),
% 0.20/0.51    inference(avatar_component_clause,[],[f150])).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    spl3_18 <=> r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    ~spl3_18 | ~spl3_13 | spl3_17),
% 0.20/0.51    inference(avatar_split_clause,[],[f147,f143,f122,f150])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    spl3_13 <=> ! [X0] : k4_xboole_0(k1_relat_1(sK2),X0) = k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.51  fof(f143,plain,(
% 0.20/0.51    spl3_17 <=> r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    ~r1_xboole_0(sK0,k4_xboole_0(k1_relat_1(sK2),sK1)) | (~spl3_13 | spl3_17)),
% 0.20/0.51    inference(forward_demodulation,[],[f145,f123])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(k1_relat_1(sK2),X0) = k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)))) ) | ~spl3_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f122])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    ~r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))) | spl3_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f143])).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    ~spl3_16 | ~spl3_17 | spl3_3 | ~spl3_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f77,f70,f46,f143,f139])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    spl3_3 <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    spl3_8 <=> ! [X1,X0] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ~r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))) | ~v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))) | (spl3_3 | ~spl3_8)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(sK0,k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)))) | ~v1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1))) | (spl3_3 | ~spl3_8)),
% 0.20/0.51    inference(superposition,[],[f48,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl3_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f70])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0) | spl3_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f46])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    spl3_13 | ~spl3_1 | ~spl3_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f82,f79,f36,f122])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    spl3_9 <=> ! [X1,X0] : (k4_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.51  % (17393)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    ( ! [X0] : (k4_xboole_0(k1_relat_1(sK2),X0) = k1_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,X0)))) ) | (~spl3_1 | ~spl3_9)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f38,f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0))) | ~v1_relat_1(X1)) ) | ~spl3_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f79])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    spl3_11 | ~spl3_1 | ~spl3_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f62,f55,f36,f90])).
% 0.20/0.51  % (17396)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    spl3_5 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) ) | (~spl3_1 | ~spl3_5)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f38,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f55])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    spl3_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f34,f86])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k7_relat_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k7_relat_1(X2,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f33,f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : k6_subset_1(X0,X1) = k4_xboole_0(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k4_xboole_0(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f28,f25])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    spl3_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f32,f79])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k4_xboole_0(X1,k7_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f31,f25])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k4_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f27,f25])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1] : (k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) = k6_subset_1(k1_relat_1(X1),X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    spl3_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f24,f70])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k7_relat_1(X0,X1) = k1_xboole_0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    spl3_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f29,f64])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    spl3_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f26,f55])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    spl3_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f23,f51])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ~spl3_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f30,f46])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    k1_xboole_0 != k7_relat_1(k4_xboole_0(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.20/0.51    inference(forward_demodulation,[],[f22,f25])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f8])).
% 0.20/0.51  fof(f8,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    spl3_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f21,f41])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    r1_tarski(sK0,sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    spl3_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f20,f36])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    v1_relat_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (17389)------------------------------
% 0.20/0.51  % (17389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (17389)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (17389)Memory used [KB]: 6140
% 0.20/0.51  % (17389)Time elapsed: 0.067 s
% 0.20/0.51  % (17389)------------------------------
% 0.20/0.51  % (17389)------------------------------
% 0.20/0.51  % (17385)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.51  % (17384)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.51  % (17383)Success in time 0.156 s
%------------------------------------------------------------------------------
