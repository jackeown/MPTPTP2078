%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 116 expanded)
%              Number of leaves         :   17 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  179 ( 301 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f48,f66,f71,f82,f95,f122,f155])).

fof(f155,plain,
    ( ~ spl5_4
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl5_4
    | spl5_6 ),
    inference(resolution,[],[f139,f25])).

fof(f25,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1)
      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( ( r1_tarski(X2,X3)
            & r1_tarski(X0,X1) )
         => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).

fof(f139,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl5_4
    | spl5_6 ),
    inference(resolution,[],[f101,f81])).

fof(f81,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_6
  <=> r1_tarski(k1_relat_1(sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f101,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(sK4),X0)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl5_4 ),
    inference(superposition,[],[f36,f90])).

fof(f90,plain,
    ( sK0 = k2_xboole_0(k1_relat_1(sK4),sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f70,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f70,plain,
    ( r1_tarski(k1_relat_1(sK4),sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_4
  <=> r1_tarski(k1_relat_1(sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f122,plain,
    ( spl5_5
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl5_5
    | ~ spl5_8 ),
    inference(resolution,[],[f106,f26])).

fof(f26,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f106,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl5_5
    | ~ spl5_8 ),
    inference(resolution,[],[f96,f78])).

fof(f78,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK3)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_5
  <=> r1_tarski(k2_relat_1(sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f96,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(sK4),X0)
        | ~ r1_tarski(sK2,X0) )
    | ~ spl5_8 ),
    inference(superposition,[],[f36,f94])).

fof(f94,plain,
    ( sK2 = k2_xboole_0(k2_relat_1(sK4),sK2)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl5_8
  <=> sK2 = k2_xboole_0(k2_relat_1(sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f95,plain,
    ( spl5_8
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f91,f41,f93])).

fof(f41,plain,
    ( spl5_1
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f91,plain,
    ( ~ v1_relat_1(sK4)
    | sK2 = k2_xboole_0(k2_relat_1(sK4),sK2) ),
    inference(resolution,[],[f56,f60])).

fof(f60,plain,(
    v5_relat_1(sK4,sK2) ),
    inference(resolution,[],[f38,f24])).

fof(f24,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f56,plain,(
    ! [X2,X3] :
      ( ~ v5_relat_1(X2,X3)
      | ~ v1_relat_1(X2)
      | k2_xboole_0(k2_relat_1(X2),X3) = X3 ) ),
    inference(resolution,[],[f32,f33])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f82,plain,
    ( ~ spl5_1
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f72,f80,f77,f41])).

fof(f72,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,(
    ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f71,plain,
    ( ~ spl5_1
    | spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f67,f63,f69,f41])).

fof(f63,plain,
    ( spl5_3
  <=> sK4 = k7_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f67,plain,
    ( r1_tarski(k1_relat_1(sK4),sK0)
    | ~ v1_relat_1(sK4)
    | ~ spl5_3 ),
    inference(superposition,[],[f30,f64])).

fof(f64,plain,
    ( sK4 = k7_relat_1(sK4,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f66,plain,
    ( spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f61,f41,f63])).

fof(f61,plain,
    ( ~ v1_relat_1(sK4)
    | sK4 = k7_relat_1(sK4,sK0) ),
    inference(resolution,[],[f34,f59])).

fof(f59,plain,(
    v4_relat_1(sK4,sK0) ),
    inference(resolution,[],[f37,f24])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f48,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | spl5_2 ),
    inference(resolution,[],[f45,f29])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f45,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl5_2
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f46,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f39,f44,f41])).

fof(f39,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK2))
    | v1_relat_1(sK4) ),
    inference(resolution,[],[f28,f24])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:00:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (31752)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.48  % (31752)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f46,f48,f66,f71,f82,f95,f122,f155])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ~spl5_4 | spl5_6),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    $false | (~spl5_4 | spl5_6)),
% 0.21/0.48    inference(resolution,[],[f139,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & r1_tarski(X2,X3) & r1_tarski(X0,X1) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4] : ((~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & (r1_tarski(X2,X3) & r1_tarski(X0,X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ~r1_tarski(sK0,sK1) | (~spl5_4 | spl5_6)),
% 0.21/0.48    inference(resolution,[],[f101,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ~r1_tarski(k1_relat_1(sK4),sK1) | spl5_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl5_6 <=> r1_tarski(k1_relat_1(sK4),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_relat_1(sK4),X0) | ~r1_tarski(sK0,X0)) ) | ~spl5_4),
% 0.21/0.48    inference(superposition,[],[f36,f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    sK0 = k2_xboole_0(k1_relat_1(sK4),sK0) | ~spl5_4),
% 0.21/0.48    inference(resolution,[],[f70,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    r1_tarski(k1_relat_1(sK4),sK0) | ~spl5_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl5_4 <=> r1_tarski(k1_relat_1(sK4),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl5_5 | ~spl5_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    $false | (spl5_5 | ~spl5_8)),
% 0.21/0.49    inference(resolution,[],[f106,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    r1_tarski(sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    ~r1_tarski(sK2,sK3) | (spl5_5 | ~spl5_8)),
% 0.21/0.49    inference(resolution,[],[f96,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK4),sK3) | spl5_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl5_5 <=> r1_tarski(k2_relat_1(sK4),sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k2_relat_1(sK4),X0) | ~r1_tarski(sK2,X0)) ) | ~spl5_8),
% 0.21/0.49    inference(superposition,[],[f36,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    sK2 = k2_xboole_0(k2_relat_1(sK4),sK2) | ~spl5_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl5_8 <=> sK2 = k2_xboole_0(k2_relat_1(sK4),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl5_8 | ~spl5_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f91,f41,f93])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    spl5_1 <=> v1_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ~v1_relat_1(sK4) | sK2 = k2_xboole_0(k2_relat_1(sK4),sK2)),
% 0.21/0.49    inference(resolution,[],[f56,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    v5_relat_1(sK4,sK2)),
% 0.21/0.49    inference(resolution,[],[f38,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~v5_relat_1(X2,X3) | ~v1_relat_1(X2) | k2_xboole_0(k2_relat_1(X2),X3) = X3) )),
% 0.21/0.49    inference(resolution,[],[f32,f33])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ~spl5_1 | ~spl5_5 | ~spl5_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f72,f80,f77,f41])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ~r1_tarski(k1_relat_1(sK4),sK1) | ~r1_tarski(k2_relat_1(sK4),sK3) | ~v1_relat_1(sK4)),
% 0.21/0.49    inference(resolution,[],[f35,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ~spl5_1 | spl5_4 | ~spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f67,f63,f69,f41])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl5_3 <=> sK4 = k7_relat_1(sK4,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    r1_tarski(k1_relat_1(sK4),sK0) | ~v1_relat_1(sK4) | ~spl5_3),
% 0.21/0.49    inference(superposition,[],[f30,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    sK4 = k7_relat_1(sK4,sK0) | ~spl5_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl5_3 | ~spl5_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f61,f41,f63])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ~v1_relat_1(sK4) | sK4 = k7_relat_1(sK4,sK0)),
% 0.21/0.49    inference(resolution,[],[f34,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    v4_relat_1(sK4,sK0)),
% 0.21/0.49    inference(resolution,[],[f37,f24])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    spl5_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    $false | spl5_2),
% 0.21/0.49    inference(resolution,[],[f45,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    spl5_2 <=> v1_relat_1(k2_zfmisc_1(sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    spl5_1 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f44,f41])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ~v1_relat_1(k2_zfmisc_1(sK0,sK2)) | v1_relat_1(sK4)),
% 0.21/0.49    inference(resolution,[],[f28,f24])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (31752)------------------------------
% 0.21/0.49  % (31752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31752)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (31752)Memory used [KB]: 10618
% 0.21/0.49  % (31752)Time elapsed: 0.043 s
% 0.21/0.49  % (31752)------------------------------
% 0.21/0.49  % (31752)------------------------------
% 0.21/0.49  % (31757)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.49  % (31737)Success in time 0.125 s
%------------------------------------------------------------------------------
