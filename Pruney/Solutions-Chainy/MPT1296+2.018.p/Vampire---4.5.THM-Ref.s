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
% DateTime   : Thu Dec  3 13:13:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 129 expanded)
%              Number of leaves         :   19 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :  176 ( 313 expanded)
%              Number of equality atoms :   60 ( 112 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f51,f57,f64,f69,f81,f86,f97,f110,f114])).

fof(f114,plain,
    ( spl2_3
    | ~ spl2_6
    | spl2_8
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl2_3
    | ~ spl2_6
    | spl2_8
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f112,f44])).

fof(f44,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_3
  <=> k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f112,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    | ~ spl2_6
    | spl2_8
    | ~ spl2_9
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f111,f102])).

fof(f102,plain,
    ( k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | ~ spl2_6
    | spl2_8
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f99,f63])).

fof(f63,plain,
    ( sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_6
  <=> sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f99,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | spl2_8
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f80,f85,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tops_2)).

fof(f85,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_9
  <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f80,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,sK1)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_8
  <=> k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f111,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))))
    | ~ spl2_11 ),
    inference(unit_resulting_resolution,[],[f109,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f109,plain,
    ( m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl2_11
  <=> m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f110,plain,
    ( spl2_11
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f90,f83,f107])).

fof(f90,plain,
    ( m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f85,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f97,plain,
    ( ~ spl2_10
    | spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f87,f83,f78,f94])).

fof(f94,plain,
    ( spl2_10
  <=> k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f87,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))
    | spl2_8
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f80,f85,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          | k7_setfam_1(X0,X1) = k1_xboole_0 )
        & ( k7_setfam_1(X0,X1) != k1_xboole_0
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ~ ( k1_xboole_0 = X1
            & k7_setfam_1(X0,X1) != k1_xboole_0 )
        & ~ ( k7_setfam_1(X0,X1) = k1_xboole_0
            & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tops_2)).

fof(f86,plain,
    ( spl2_9
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f70,f37,f83])).

fof(f37,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f70,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f39,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f39,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f81,plain,
    ( ~ spl2_8
    | spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f73,f37,f32,f78])).

fof(f32,plain,
    ( spl2_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f73,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,sK1)
    | spl2_1
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f34,f39,f27])).

fof(f34,plain,
    ( k1_xboole_0 != sK1
    | spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f69,plain,
    ( spl2_7
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f58,f54,f66])).

fof(f66,plain,
    ( spl2_7
  <=> k5_setfam_1(sK0,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f54,plain,
    ( spl2_5
  <=> m1_subset_1(k5_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f58,plain,
    ( k5_setfam_1(sK0,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,sK1)))
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f56,f23])).

fof(f56,plain,
    ( m1_subset_1(k5_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f64,plain,
    ( spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f59,f37,f61])).

fof(f59,plain,
    ( sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f39,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f57,plain,
    ( spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f52,f37,f54])).

fof(f52,plain,
    ( m1_subset_1(k5_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f39,f24])).

fof(f51,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f46,f37,f48])).

fof(f48,plain,
    ( spl2_4
  <=> sK1 = k3_subset_1(k1_zfmisc_1(sK0),k3_subset_1(k1_zfmisc_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f46,plain,
    ( sK1 = k3_subset_1(k1_zfmisc_1(sK0),k3_subset_1(k1_zfmisc_1(sK0),sK1))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f39,f23])).

fof(f45,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f22,f42])).

fof(f22,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tops_2)).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f20,f37])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f32])).

fof(f21,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:42:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (10104)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (10110)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (10102)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (10110)Refutation not found, incomplete strategy% (10110)------------------------------
% 0.21/0.48  % (10110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10110)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (10110)Memory used [KB]: 1535
% 0.21/0.48  % (10110)Time elapsed: 0.030 s
% 0.21/0.48  % (10110)------------------------------
% 0.21/0.48  % (10110)------------------------------
% 0.21/0.49  % (10104)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f35,f40,f45,f51,f57,f64,f69,f81,f86,f97,f110,f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl2_3 | ~spl2_6 | spl2_8 | ~spl2_9 | ~spl2_11),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f113])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    $false | (spl2_3 | ~spl2_6 | spl2_8 | ~spl2_9 | ~spl2_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f112,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) | spl2_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    spl2_3 <=> k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) | (~spl2_6 | spl2_8 | ~spl2_9 | ~spl2_11)),
% 0.21/0.49    inference(forward_demodulation,[],[f111,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | (~spl2_6 | spl2_8 | ~spl2_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f99,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) | ~spl2_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl2_6 <=> sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | (spl2_8 | ~spl2_9)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f80,f85,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : ((k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tops_2)).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl2_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl2_9 <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    k1_xboole_0 != k7_setfam_1(sK0,sK1) | spl2_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl2_8 <=> k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))) | ~spl2_11),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f109,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl2_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f107])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl2_11 <=> m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl2_11 | ~spl2_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f90,f83,f107])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl2_9),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f85,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ~spl2_10 | spl2_8 | ~spl2_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f87,f83,f78,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl2_10 <=> k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    k1_xboole_0 != k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) | (spl2_8 | ~spl2_9)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f80,f85,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k7_setfam_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (((k1_xboole_0 != X1 | k7_setfam_1(X0,X1) = k1_xboole_0) & (k7_setfam_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (~(k1_xboole_0 = X1 & k7_setfam_1(X0,X1) != k1_xboole_0) & ~(k7_setfam_1(X0,X1) = k1_xboole_0 & k1_xboole_0 != X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tops_2)).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl2_9 | ~spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f70,f37,f83])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl2_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f39,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl2_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f37])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ~spl2_8 | spl2_1 | ~spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f73,f37,f32,f78])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    spl2_1 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    k1_xboole_0 != k7_setfam_1(sK0,sK1) | (spl2_1 | ~spl2_2)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f34,f39,f27])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | spl2_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f32])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl2_7 | ~spl2_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f58,f54,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl2_7 <=> k5_setfam_1(sK0,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl2_5 <=> m1_subset_1(k5_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    k5_setfam_1(sK0,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,k5_setfam_1(sK0,sK1))) | ~spl2_5),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f56,f23])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    m1_subset_1(k5_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f54])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl2_6 | ~spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f59,f37,f61])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) | ~spl2_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f39,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl2_5 | ~spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f37,f54])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    m1_subset_1(k5_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f39,f24])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl2_4 | ~spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f37,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    spl2_4 <=> sK1 = k3_subset_1(k1_zfmisc_1(sK0),k3_subset_1(k1_zfmisc_1(sK0),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    sK1 = k3_subset_1(k1_zfmisc_1(sK0),k3_subset_1(k1_zfmisc_1(sK0),sK1)) | ~spl2_2),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f39,f23])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ~spl2_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f42])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1] : ((k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tops_2)).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    spl2_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f37])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ~spl2_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f32])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    k1_xboole_0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (10104)------------------------------
% 0.21/0.49  % (10104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10104)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (10104)Memory used [KB]: 1663
% 0.21/0.49  % (10104)Time elapsed: 0.062 s
% 0.21/0.49  % (10104)------------------------------
% 0.21/0.49  % (10104)------------------------------
% 0.21/0.50  % (10096)Success in time 0.132 s
%------------------------------------------------------------------------------
