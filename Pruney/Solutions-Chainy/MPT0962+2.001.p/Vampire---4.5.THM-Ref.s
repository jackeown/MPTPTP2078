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
% DateTime   : Thu Dec  3 13:00:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 126 expanded)
%              Number of leaves         :   16 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :  228 ( 400 expanded)
%              Number of equality atoms :   35 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f97,f104,f113,f126,f163,f188,f197,f208,f213,f230])).

fof(f230,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_16
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_16
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f228,f91])).

fof(f91,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f228,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl3_2
    | spl3_16
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f227,f96])).

fof(f96,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f227,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl3_16
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f220,f207])).

fof(f207,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl3_16
  <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f220,plain,
    ( v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_17 ),
    inference(superposition,[],[f60,f212])).

fof(f212,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl3_17
  <=> k1_xboole_0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f60,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f213,plain,
    ( spl3_17
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f200,f194,f210])).

fof(f194,plain,
    ( spl3_15
  <=> r1_tarski(k2_relat_1(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f200,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl3_15 ),
    inference(resolution,[],[f196,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f196,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f194])).

fof(f208,plain,
    ( ~ spl3_16
    | spl3_4
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f191,f185,f106,f205])).

fof(f106,plain,
    ( spl3_4
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f185,plain,
    ( spl3_14
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f191,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | spl3_4
    | ~ spl3_14 ),
    inference(superposition,[],[f108,f187])).

fof(f187,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f185])).

fof(f108,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f197,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f192,f185,f101,f194])).

fof(f101,plain,
    ( spl3_3
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f192,plain,
    ( r1_tarski(k2_relat_1(sK1),k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(superposition,[],[f103,f187])).

fof(f103,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f188,plain,
    ( spl3_14
    | spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f183,f110,f106,f185])).

fof(f110,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f183,plain,
    ( k1_xboole_0 = sK0
    | spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f115,f111])).

fof(f111,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f115,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl3_4 ),
    inference(subsumption_resolution,[],[f114,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f114,plain,
    ( k1_xboole_0 = sK0
    | k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl3_4 ),
    inference(resolution,[],[f108,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f163,plain,
    ( ~ spl3_3
    | spl3_5
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl3_3
    | spl3_5
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f159,f112])).

fof(f112,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f159,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f128,f103])).

fof(f128,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(sK1),X1)
        | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),X1))) )
    | ~ spl3_7 ),
    inference(resolution,[],[f125,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

% (31307)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f125,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f126,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f99,f94,f89,f123])).

fof(f99,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f98,f91])).

fof(f98,plain,
    ( ~ v1_relat_1(sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))
    | ~ spl3_2 ),
    inference(resolution,[],[f96,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f113,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f87,f110,f106])).

fof(f87,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    inference(global_subsumption,[],[f47,f45])).

fof(f45,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f47,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f104,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f48,f101])).

% (31311)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f48,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f97,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f47,f94])).

fof(f92,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f46,f89])).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (31319)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.46  % (31313)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (31306)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (31304)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.46  % (31312)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (31304)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (31301)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f235,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f92,f97,f104,f113,f126,f163,f188,f197,f208,f213,f230])).
% 0.20/0.48  fof(f230,plain,(
% 0.20/0.48    ~spl3_1 | ~spl3_2 | spl3_16 | ~spl3_17),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f229])).
% 0.20/0.48  fof(f229,plain,(
% 0.20/0.48    $false | (~spl3_1 | ~spl3_2 | spl3_16 | ~spl3_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f228,f91])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    v1_relat_1(sK1) | ~spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f89])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    spl3_1 <=> v1_relat_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f228,plain,(
% 0.20/0.48    ~v1_relat_1(sK1) | (~spl3_2 | spl3_16 | ~spl3_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f227,f96])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    v1_funct_1(sK1) | ~spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f94])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    spl3_2 <=> v1_funct_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f227,plain,(
% 0.20/0.48    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | (spl3_16 | ~spl3_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f220,f207])).
% 0.20/0.48  fof(f207,plain,(
% 0.20/0.48    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | spl3_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f205])).
% 0.20/0.48  fof(f205,plain,(
% 0.20/0.48    spl3_16 <=> v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.48  fof(f220,plain,(
% 0.20/0.48    v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl3_17),
% 0.20/0.48    inference(superposition,[],[f60,f212])).
% 0.20/0.48  fof(f212,plain,(
% 0.20/0.48    k1_xboole_0 = k2_relat_1(sK1) | ~spl3_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f210])).
% 0.20/0.48  fof(f210,plain,(
% 0.20/0.48    spl3_17 <=> k1_xboole_0 = k2_relat_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.48  fof(f213,plain,(
% 0.20/0.48    spl3_17 | ~spl3_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f200,f194,f210])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    spl3_15 <=> r1_tarski(k2_relat_1(sK1),k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    k1_xboole_0 = k2_relat_1(sK1) | ~spl3_15),
% 0.20/0.48    inference(resolution,[],[f196,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.48  fof(f196,plain,(
% 0.20/0.48    r1_tarski(k2_relat_1(sK1),k1_xboole_0) | ~spl3_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f194])).
% 0.20/0.48  fof(f208,plain,(
% 0.20/0.48    ~spl3_16 | spl3_4 | ~spl3_14),
% 0.20/0.48    inference(avatar_split_clause,[],[f191,f185,f106,f205])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    spl3_4 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.48  fof(f185,plain,(
% 0.20/0.48    spl3_14 <=> k1_xboole_0 = sK0),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.48  fof(f191,plain,(
% 0.20/0.48    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | (spl3_4 | ~spl3_14)),
% 0.20/0.48    inference(superposition,[],[f108,f187])).
% 0.20/0.48  fof(f187,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | ~spl3_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f185])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl3_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f106])).
% 0.20/0.48  fof(f197,plain,(
% 0.20/0.48    spl3_15 | ~spl3_3 | ~spl3_14),
% 0.20/0.48    inference(avatar_split_clause,[],[f192,f185,f101,f194])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    spl3_3 <=> r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    r1_tarski(k2_relat_1(sK1),k1_xboole_0) | (~spl3_3 | ~spl3_14)),
% 0.20/0.48    inference(superposition,[],[f103,f187])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    r1_tarski(k2_relat_1(sK1),sK0) | ~spl3_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f101])).
% 0.20/0.48  fof(f188,plain,(
% 0.20/0.48    spl3_14 | spl3_4 | ~spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f183,f110,f106,f185])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.48  fof(f183,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | (spl3_4 | ~spl3_5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f115,f111])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl3_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f110])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl3_4),
% 0.20/0.48    inference(subsumption_resolution,[],[f114,f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | k1_relat_1(sK1) != k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl3_4),
% 0.20/0.48    inference(resolution,[],[f108,f77])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(flattening,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.48  fof(f163,plain,(
% 0.20/0.48    ~spl3_3 | spl3_5 | ~spl3_7),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f162])).
% 0.20/0.48  fof(f162,plain,(
% 0.20/0.48    $false | (~spl3_3 | spl3_5 | ~spl3_7)),
% 0.20/0.48    inference(subsumption_resolution,[],[f159,f112])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl3_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f110])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | (~spl3_3 | ~spl3_7)),
% 0.20/0.48    inference(resolution,[],[f128,f103])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ( ! [X1] : (~r1_tarski(k2_relat_1(sK1),X1) | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),X1)))) ) | ~spl3_7),
% 0.20/0.48    inference(resolution,[],[f125,f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.20/0.48    inference(flattening,[],[f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 0.20/0.48  % (31307)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | ~spl3_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f123])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    spl3_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    spl3_7 | ~spl3_1 | ~spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f99,f94,f89,f123])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | (~spl3_1 | ~spl3_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f98,f91])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ~v1_relat_1(sK1) | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) | ~spl3_2),
% 0.20/0.48    inference(resolution,[],[f96,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    ~spl3_4 | ~spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f87,f110,f106])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.20/0.48    inference(global_subsumption,[],[f47,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ~v1_funct_1(sK1) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.48    inference(negated_conjecture,[],[f20])).
% 0.20/0.48  fof(f20,conjecture,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    v1_funct_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f48,f101])).
% 0.20/0.48  % (31311)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f47,f94])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    spl3_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f46,f89])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    v1_relat_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (31304)------------------------------
% 0.20/0.48  % (31304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (31304)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (31304)Memory used [KB]: 10746
% 0.20/0.48  % (31304)Time elapsed: 0.065 s
% 0.20/0.48  % (31304)------------------------------
% 0.20/0.48  % (31304)------------------------------
% 0.20/0.49  % (31300)Success in time 0.132 s
%------------------------------------------------------------------------------
