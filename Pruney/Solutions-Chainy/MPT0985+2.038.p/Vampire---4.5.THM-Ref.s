%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 547 expanded)
%              Number of leaves         :   44 ( 211 expanded)
%              Depth                    :   12
%              Number of atoms          :  628 (1598 expanded)
%              Number of equality atoms :  101 ( 281 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (14214)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f802,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f85,f97,f104,f108,f112,f136,f143,f147,f178,f202,f214,f218,f230,f252,f289,f317,f386,f387,f421,f428,f499,f507,f580,f646,f690,f786,f787,f801])).

fof(f801,plain,
    ( spl5_8
    | ~ spl5_27
    | ~ spl5_35
    | ~ spl5_76 ),
    inference(avatar_contradiction_clause,[],[f800])).

fof(f800,plain,
    ( $false
    | spl5_8
    | ~ spl5_27
    | ~ spl5_35
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f799,f645])).

fof(f645,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f644])).

fof(f644,plain,
    ( spl5_76
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f799,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | spl5_8
    | ~ spl5_27
    | ~ spl5_35 ),
    inference(forward_demodulation,[],[f798,f316])).

fof(f316,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl5_35
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f798,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl5_8
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f797,f77])).

fof(f77,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f797,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl5_8
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f139,f251])).

fof(f251,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl5_27
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f139,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl5_8
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f787,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_funct_1(k1_xboole_0)
    | sK1 != k1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 != sK1
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f786,plain,
    ( spl5_53
    | ~ spl5_65
    | ~ spl5_83
    | ~ spl5_87 ),
    inference(avatar_contradiction_clause,[],[f785])).

fof(f785,plain,
    ( $false
    | spl5_53
    | ~ spl5_65
    | ~ spl5_83
    | ~ spl5_87 ),
    inference(subsumption_resolution,[],[f720,f784])).

fof(f784,plain,
    ( ! [X14] : v1_funct_2(k1_xboole_0,k1_xboole_0,X14)
    | ~ spl5_65
    | ~ spl5_87 ),
    inference(subsumption_resolution,[],[f779,f783])).

fof(f783,plain,
    ( ! [X10,X11] : k1_xboole_0 = k1_relset_1(X10,X11,k1_xboole_0)
    | ~ spl5_65
    | ~ spl5_87 ),
    inference(forward_demodulation,[],[f775,f704])).

fof(f704,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_87 ),
    inference(avatar_component_clause,[],[f703])).

fof(f703,plain,
    ( spl5_87
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f775,plain,
    ( ! [X10,X11] : k1_relat_1(k1_xboole_0) = k1_relset_1(X10,X11,k1_xboole_0)
    | ~ spl5_65 ),
    inference(resolution,[],[f716,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f716,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl5_65 ),
    inference(superposition,[],[f52,f680])).

fof(f680,plain,
    ( ! [X0] : k1_xboole_0 = sK3(X0)
    | ~ spl5_65 ),
    inference(forward_demodulation,[],[f678,f676])).

fof(f676,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl5_65 ),
    inference(resolution,[],[f582,f70])).

fof(f70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f582,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k2_funct_1(k1_xboole_0) = X0 )
    | ~ spl5_65 ),
    inference(resolution,[],[f579,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f579,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f578])).

fof(f578,plain,
    ( spl5_65
  <=> v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f678,plain,
    ( ! [X0] : sK3(X0) = k2_funct_1(k1_xboole_0)
    | ~ spl5_65 ),
    inference(resolution,[],[f582,f53])).

fof(f53,plain,(
    ! [X0] : v1_xboole_0(sK3(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f779,plain,
    ( ! [X14] :
        ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X14,k1_xboole_0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X14) )
    | ~ spl5_65 ),
    inference(resolution,[],[f716,f72])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f720,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl5_53
    | ~ spl5_83 ),
    inference(superposition,[],[f427,f689])).

fof(f689,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl5_83 ),
    inference(avatar_component_clause,[],[f688])).

fof(f688,plain,
    ( spl5_83
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f427,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl5_53 ),
    inference(avatar_component_clause,[],[f426])).

fof(f426,plain,
    ( spl5_53
  <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f690,plain,
    ( spl5_83
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f676,f578,f688])).

fof(f646,plain,
    ( spl5_76
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_27
    | ~ spl5_35
    | ~ spl5_58
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f527,f505,f497,f315,f250,f200,f176,f644])).

fof(f176,plain,
    ( spl5_15
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f200,plain,
    ( spl5_19
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f497,plain,
    ( spl5_58
  <=> v1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f505,plain,
    ( spl5_60
  <=> v1_funct_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f527,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_27
    | ~ spl5_35
    | ~ spl5_58
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f526,f77])).

fof(f526,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0))))
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_27
    | ~ spl5_35
    | ~ spl5_58
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f525,f251])).

fof(f525,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0))))
    | ~ spl5_15
    | ~ spl5_19
    | ~ spl5_35
    | ~ spl5_58
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f524,f357])).

fof(f357,plain,
    ( sK1 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl5_15
    | ~ spl5_35 ),
    inference(superposition,[],[f177,f316])).

fof(f177,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f176])).

fof(f524,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_relat_1(k1_xboole_0))))
    | ~ spl5_19
    | ~ spl5_35
    | ~ spl5_58
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f523,f361])).

fof(f361,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl5_19
    | ~ spl5_35 ),
    inference(superposition,[],[f201,f316])).

fof(f201,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f200])).

fof(f523,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ spl5_58
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f517,f498])).

fof(f498,plain,
    ( v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f497])).

fof(f517,plain,
    ( ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0)))))
    | ~ spl5_60 ),
    inference(resolution,[],[f506,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f506,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f505])).

fof(f580,plain,
    ( spl5_65
    | ~ spl5_27
    | ~ spl5_35
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f560,f384,f315,f250,f578])).

fof(f384,plain,
    ( spl5_45
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f560,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl5_27
    | ~ spl5_35
    | ~ spl5_45 ),
    inference(forward_demodulation,[],[f559,f316])).

fof(f559,plain,
    ( v1_xboole_0(k2_funct_1(sK2))
    | ~ spl5_27
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f558,f70])).

fof(f558,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_funct_1(sK2))
    | ~ spl5_27
    | ~ spl5_45 ),
    inference(forward_demodulation,[],[f545,f251])).

fof(f545,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(k2_funct_1(sK2))
    | ~ spl5_45 ),
    inference(resolution,[],[f385,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f385,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f384])).

fof(f507,plain,
    ( spl5_60
    | ~ spl5_10
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f355,f315,f145,f505])).

fof(f145,plain,
    ( spl5_10
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f355,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl5_10
    | ~ spl5_35 ),
    inference(superposition,[],[f146,f316])).

fof(f146,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f499,plain,
    ( spl5_58
    | ~ spl5_4
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f350,f315,f99,f497])).

fof(f99,plain,
    ( spl5_4
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f350,plain,
    ( v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl5_4
    | ~ spl5_35 ),
    inference(superposition,[],[f100,f316])).

fof(f100,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f428,plain,
    ( ~ spl5_53
    | spl5_9
    | ~ spl5_27
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f424,f315,f250,f141,f426])).

fof(f141,plain,
    ( spl5_9
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f424,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl5_9
    | ~ spl5_27
    | ~ spl5_35 ),
    inference(forward_demodulation,[],[f423,f316])).

fof(f423,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl5_9
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f142,f251])).

fof(f142,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f141])).

fof(f421,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f387,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f386,plain,
    ( spl5_45
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f157,f145,f110,f106,f99,f83,f79,f384])).

fof(f79,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f83,plain,
    ( spl5_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f106,plain,
    ( spl5_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f110,plain,
    ( spl5_7
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f157,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f156,f128])).

fof(f128,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f127,f122])).

fof(f122,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f113,f111])).

fof(f111,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f113,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl5_6 ),
    inference(resolution,[],[f107,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f107,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f127,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f92,f120])).

fof(f120,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_6 ),
    inference(resolution,[],[f107,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f92,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f90,f80])).

fof(f80,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f90,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f84,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f84,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f156,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f155,f126])).

fof(f126,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f93,f120])).

fof(f93,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f91,f80])).

fof(f91,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f84,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f155,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f149,f100])).

fof(f149,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl5_10 ),
    inference(resolution,[],[f146,f62])).

fof(f317,plain,
    ( spl5_35
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f306,f161,f315])).

fof(f161,plain,
    ( spl5_11
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f306,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_11 ),
    inference(resolution,[],[f290,f70])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK2 = X0 )
    | ~ spl5_11 ),
    inference(resolution,[],[f162,f48])).

fof(f162,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f161])).

fof(f289,plain,
    ( spl5_11
    | ~ spl5_23
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f288,f250,f216,f161])).

fof(f216,plain,
    ( spl5_23
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f288,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_23
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f287,f70])).

fof(f287,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK2)
    | ~ spl5_23
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f233,f251])).

fof(f233,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ spl5_23 ),
    inference(resolution,[],[f217,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f217,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f216])).

fof(f252,plain,
    ( spl5_26
    | spl5_27
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f123,f106,f95,f250,f247])).

fof(f247,plain,
    ( spl5_26
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f95,plain,
    ( spl5_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f123,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f118,f96])).

fof(f96,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f107,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f230,plain,
    ( spl5_24
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f154,f145,f110,f106,f99,f83,f79,f228])).

fof(f228,plain,
    ( spl5_24
  <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f154,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f153,f128])).

fof(f153,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f152,f126])).

fof(f152,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f148,f100])).

fof(f148,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl5_10 ),
    inference(resolution,[],[f146,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f218,plain,
    ( spl5_23
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f132,f110,f106,f79,f216])).

fof(f132,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl5_1
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f131,f122])).

fof(f131,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl5_1
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f87,f120])).

fof(f87,plain,
    ( ~ v1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl5_1 ),
    inference(resolution,[],[f80,f62])).

fof(f214,plain,
    ( spl5_22
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f119,f106,f212])).

fof(f212,plain,
    ( spl5_22
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f119,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl5_6 ),
    inference(resolution,[],[f107,f63])).

fof(f202,plain,
    ( spl5_19
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f126,f106,f83,f79,f200])).

fof(f178,plain,
    ( spl5_15
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f128,f110,f106,f83,f79,f176])).

fof(f147,plain,
    ( spl5_10
    | ~ spl5_1
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f129,f106,f79,f145])).

fof(f129,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f89,f120])).

fof(f89,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f80,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f143,plain,
    ( ~ spl5_8
    | ~ spl5_9
    | ~ spl5_1
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f130,f106,f79,f141,f138])).

fof(f130,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_1
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f38,f129])).

fof(f38,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

% (14210)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f136,plain,
    ( spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f120,f106,f102])).

fof(f102,plain,
    ( spl5_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f112,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f43,f110])).

fof(f43,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f108,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f41,f106])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f104,plain,
    ( spl5_4
    | ~ spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f88,f79,f102,f99])).

fof(f88,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f80,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f40,f95])).

fof(f40,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f85,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f42,f83])).

fof(f42,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f81,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f39,f79])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:23:36 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.46  % (14219)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (14206)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (14220)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (14212)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (14222)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (14219)Refutation not found, incomplete strategy% (14219)------------------------------
% 0.22/0.49  % (14219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (14219)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (14219)Memory used [KB]: 1663
% 0.22/0.49  % (14219)Time elapsed: 0.058 s
% 0.22/0.49  % (14219)------------------------------
% 0.22/0.49  % (14219)------------------------------
% 0.22/0.49  % (14206)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  % (14214)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  fof(f802,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f81,f85,f97,f104,f108,f112,f136,f143,f147,f178,f202,f214,f218,f230,f252,f289,f317,f386,f387,f421,f428,f499,f507,f580,f646,f690,f786,f787,f801])).
% 0.22/0.49  fof(f801,plain,(
% 0.22/0.49    spl5_8 | ~spl5_27 | ~spl5_35 | ~spl5_76),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f800])).
% 0.22/0.49  fof(f800,plain,(
% 0.22/0.49    $false | (spl5_8 | ~spl5_27 | ~spl5_35 | ~spl5_76)),
% 0.22/0.49    inference(subsumption_resolution,[],[f799,f645])).
% 0.22/0.49  fof(f645,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl5_76),
% 0.22/0.49    inference(avatar_component_clause,[],[f644])).
% 0.22/0.49  fof(f644,plain,(
% 0.22/0.49    spl5_76 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 0.22/0.49  fof(f799,plain,(
% 0.22/0.49    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (spl5_8 | ~spl5_27 | ~spl5_35)),
% 0.22/0.49    inference(forward_demodulation,[],[f798,f316])).
% 0.22/0.49  fof(f316,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | ~spl5_35),
% 0.22/0.49    inference(avatar_component_clause,[],[f315])).
% 0.22/0.49  fof(f315,plain,(
% 0.22/0.49    spl5_35 <=> k1_xboole_0 = sK2),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.22/0.49  fof(f798,plain,(
% 0.22/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl5_8 | ~spl5_27)),
% 0.22/0.49    inference(forward_demodulation,[],[f797,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.49    inference(equality_resolution,[],[f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.49  fof(f797,plain,(
% 0.22/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl5_8 | ~spl5_27)),
% 0.22/0.49    inference(forward_demodulation,[],[f139,f251])).
% 0.22/0.49  fof(f251,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | ~spl5_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f250])).
% 0.22/0.49  fof(f250,plain,(
% 0.22/0.49    spl5_27 <=> k1_xboole_0 = sK1),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl5_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f138])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl5_8 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.49  fof(f787,plain,(
% 0.22/0.49    k1_xboole_0 != sK2 | k1_xboole_0 != k2_funct_1(k1_xboole_0) | sK1 != k1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 != sK1 | k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f786,plain,(
% 0.22/0.49    spl5_53 | ~spl5_65 | ~spl5_83 | ~spl5_87),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f785])).
% 0.22/0.49  fof(f785,plain,(
% 0.22/0.49    $false | (spl5_53 | ~spl5_65 | ~spl5_83 | ~spl5_87)),
% 0.22/0.49    inference(subsumption_resolution,[],[f720,f784])).
% 0.22/0.49  fof(f784,plain,(
% 0.22/0.49    ( ! [X14] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X14)) ) | (~spl5_65 | ~spl5_87)),
% 0.22/0.49    inference(subsumption_resolution,[],[f779,f783])).
% 0.22/0.49  fof(f783,plain,(
% 0.22/0.49    ( ! [X10,X11] : (k1_xboole_0 = k1_relset_1(X10,X11,k1_xboole_0)) ) | (~spl5_65 | ~spl5_87)),
% 0.22/0.49    inference(forward_demodulation,[],[f775,f704])).
% 0.22/0.49  fof(f704,plain,(
% 0.22/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_87),
% 0.22/0.49    inference(avatar_component_clause,[],[f703])).
% 0.22/0.49  fof(f703,plain,(
% 0.22/0.49    spl5_87 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 0.22/0.49  fof(f775,plain,(
% 0.22/0.49    ( ! [X10,X11] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X10,X11,k1_xboole_0)) ) | ~spl5_65),
% 0.22/0.49    inference(resolution,[],[f716,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.49  fof(f716,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl5_65),
% 0.22/0.49    inference(superposition,[],[f52,f680])).
% 0.22/0.49  fof(f680,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = sK3(X0)) ) | ~spl5_65),
% 0.22/0.49    inference(forward_demodulation,[],[f678,f676])).
% 0.22/0.49  fof(f676,plain,(
% 0.22/0.49    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl5_65),
% 0.22/0.49    inference(resolution,[],[f582,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.49  fof(f582,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k2_funct_1(k1_xboole_0) = X0) ) | ~spl5_65),
% 0.22/0.49    inference(resolution,[],[f579,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.49  fof(f579,plain,(
% 0.22/0.49    v1_xboole_0(k2_funct_1(k1_xboole_0)) | ~spl5_65),
% 0.22/0.49    inference(avatar_component_clause,[],[f578])).
% 0.22/0.49  fof(f578,plain,(
% 0.22/0.49    spl5_65 <=> v1_xboole_0(k2_funct_1(k1_xboole_0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 0.22/0.49  fof(f678,plain,(
% 0.22/0.49    ( ! [X0] : (sK3(X0) = k2_funct_1(k1_xboole_0)) ) | ~spl5_65),
% 0.22/0.49    inference(resolution,[],[f582,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0] : (v1_xboole_0(sK3(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f779,plain,(
% 0.22/0.49    ( ! [X14] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X14,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X14)) ) | ~spl5_65),
% 0.22/0.49    inference(resolution,[],[f716,f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.22/0.49    inference(equality_resolution,[],[f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(flattening,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.49  fof(f720,plain,(
% 0.22/0.49    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl5_53 | ~spl5_83)),
% 0.22/0.49    inference(superposition,[],[f427,f689])).
% 0.22/0.49  fof(f689,plain,(
% 0.22/0.49    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl5_83),
% 0.22/0.49    inference(avatar_component_clause,[],[f688])).
% 0.22/0.49  fof(f688,plain,(
% 0.22/0.49    spl5_83 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).
% 0.22/0.49  fof(f427,plain,(
% 0.22/0.49    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | spl5_53),
% 0.22/0.49    inference(avatar_component_clause,[],[f426])).
% 0.22/0.49  fof(f426,plain,(
% 0.22/0.49    spl5_53 <=> v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 0.22/0.49  fof(f690,plain,(
% 0.22/0.49    spl5_83 | ~spl5_65),
% 0.22/0.49    inference(avatar_split_clause,[],[f676,f578,f688])).
% 0.22/0.49  fof(f646,plain,(
% 0.22/0.49    spl5_76 | ~spl5_15 | ~spl5_19 | ~spl5_27 | ~spl5_35 | ~spl5_58 | ~spl5_60),
% 0.22/0.49    inference(avatar_split_clause,[],[f527,f505,f497,f315,f250,f200,f176,f644])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    spl5_15 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.49  fof(f200,plain,(
% 0.22/0.49    spl5_19 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.49  fof(f497,plain,(
% 0.22/0.49    spl5_58 <=> v1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 0.22/0.49  fof(f505,plain,(
% 0.22/0.49    spl5_60 <=> v1_funct_1(k2_funct_1(k1_xboole_0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 0.22/0.49  fof(f527,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl5_15 | ~spl5_19 | ~spl5_27 | ~spl5_35 | ~spl5_58 | ~spl5_60)),
% 0.22/0.49    inference(forward_demodulation,[],[f526,f77])).
% 0.22/0.49  fof(f526,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) | (~spl5_15 | ~spl5_19 | ~spl5_27 | ~spl5_35 | ~spl5_58 | ~spl5_60)),
% 0.22/0.49    inference(forward_demodulation,[],[f525,f251])).
% 0.22/0.49  fof(f525,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0)))) | (~spl5_15 | ~spl5_19 | ~spl5_35 | ~spl5_58 | ~spl5_60)),
% 0.22/0.49    inference(forward_demodulation,[],[f524,f357])).
% 0.22/0.49  fof(f357,plain,(
% 0.22/0.49    sK1 = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl5_15 | ~spl5_35)),
% 0.22/0.49    inference(superposition,[],[f177,f316])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl5_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f176])).
% 0.22/0.49  fof(f524,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k1_relat_1(k1_xboole_0)))) | (~spl5_19 | ~spl5_35 | ~spl5_58 | ~spl5_60)),
% 0.22/0.49    inference(forward_demodulation,[],[f523,f361])).
% 0.22/0.49  fof(f361,plain,(
% 0.22/0.49    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | (~spl5_19 | ~spl5_35)),
% 0.22/0.49    inference(superposition,[],[f201,f316])).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl5_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f200])).
% 0.22/0.49  fof(f523,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0))))) | (~spl5_58 | ~spl5_60)),
% 0.22/0.49    inference(subsumption_resolution,[],[f517,f498])).
% 0.22/0.49  fof(f498,plain,(
% 0.22/0.49    v1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl5_58),
% 0.22/0.49    inference(avatar_component_clause,[],[f497])).
% 0.22/0.49  fof(f517,plain,(
% 0.22/0.49    ~v1_relat_1(k2_funct_1(k1_xboole_0)) | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(k1_xboole_0)),k2_relat_1(k2_funct_1(k1_xboole_0))))) | ~spl5_60),
% 0.22/0.49    inference(resolution,[],[f506,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.49  fof(f506,plain,(
% 0.22/0.49    v1_funct_1(k2_funct_1(k1_xboole_0)) | ~spl5_60),
% 0.22/0.49    inference(avatar_component_clause,[],[f505])).
% 0.22/0.49  fof(f580,plain,(
% 0.22/0.49    spl5_65 | ~spl5_27 | ~spl5_35 | ~spl5_45),
% 0.22/0.49    inference(avatar_split_clause,[],[f560,f384,f315,f250,f578])).
% 0.22/0.49  fof(f384,plain,(
% 0.22/0.49    spl5_45 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 0.22/0.49  fof(f560,plain,(
% 0.22/0.49    v1_xboole_0(k2_funct_1(k1_xboole_0)) | (~spl5_27 | ~spl5_35 | ~spl5_45)),
% 0.22/0.49    inference(forward_demodulation,[],[f559,f316])).
% 0.22/0.49  fof(f559,plain,(
% 0.22/0.49    v1_xboole_0(k2_funct_1(sK2)) | (~spl5_27 | ~spl5_45)),
% 0.22/0.49    inference(subsumption_resolution,[],[f558,f70])).
% 0.22/0.49  fof(f558,plain,(
% 0.22/0.49    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_funct_1(sK2)) | (~spl5_27 | ~spl5_45)),
% 0.22/0.49    inference(forward_demodulation,[],[f545,f251])).
% 0.22/0.49  fof(f545,plain,(
% 0.22/0.49    ~v1_xboole_0(sK1) | v1_xboole_0(k2_funct_1(sK2)) | ~spl5_45),
% 0.22/0.49    inference(resolution,[],[f385,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.22/0.49  fof(f385,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl5_45),
% 0.22/0.49    inference(avatar_component_clause,[],[f384])).
% 0.22/0.49  fof(f507,plain,(
% 0.22/0.49    spl5_60 | ~spl5_10 | ~spl5_35),
% 0.22/0.49    inference(avatar_split_clause,[],[f355,f315,f145,f505])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    spl5_10 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.49  fof(f355,plain,(
% 0.22/0.49    v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl5_10 | ~spl5_35)),
% 0.22/0.49    inference(superposition,[],[f146,f316])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    v1_funct_1(k2_funct_1(sK2)) | ~spl5_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f145])).
% 0.22/0.49  fof(f499,plain,(
% 0.22/0.49    spl5_58 | ~spl5_4 | ~spl5_35),
% 0.22/0.49    inference(avatar_split_clause,[],[f350,f315,f99,f497])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl5_4 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.49  fof(f350,plain,(
% 0.22/0.49    v1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl5_4 | ~spl5_35)),
% 0.22/0.49    inference(superposition,[],[f100,f316])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    v1_relat_1(k2_funct_1(sK2)) | ~spl5_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f99])).
% 0.22/0.49  fof(f428,plain,(
% 0.22/0.49    ~spl5_53 | spl5_9 | ~spl5_27 | ~spl5_35),
% 0.22/0.49    inference(avatar_split_clause,[],[f424,f315,f250,f141,f426])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    spl5_9 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.49  fof(f424,plain,(
% 0.22/0.49    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl5_9 | ~spl5_27 | ~spl5_35)),
% 0.22/0.49    inference(forward_demodulation,[],[f423,f316])).
% 0.22/0.49  fof(f423,plain,(
% 0.22/0.49    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl5_9 | ~spl5_27)),
% 0.22/0.49    inference(forward_demodulation,[],[f142,f251])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl5_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f141])).
% 0.22/0.49  fof(f421,plain,(
% 0.22/0.49    sK0 != k1_relset_1(sK0,sK1,sK2) | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f387,plain,(
% 0.22/0.49    sK0 != k1_relset_1(sK0,sK1,sK2) | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f386,plain,(
% 0.22/0.49    spl5_45 | ~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f157,f145,f110,f106,f99,f83,f79,f384])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl5_1 <=> v1_funct_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    spl5_2 <=> v2_funct_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    spl5_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    spl5_7 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | (~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_10)),
% 0.22/0.49    inference(forward_demodulation,[],[f156,f128])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_6 | ~spl5_7)),
% 0.22/0.49    inference(forward_demodulation,[],[f127,f122])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    sK1 = k2_relat_1(sK2) | (~spl5_6 | ~spl5_7)),
% 0.22/0.49    inference(forward_demodulation,[],[f113,f111])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl5_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f110])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl5_6),
% 0.22/0.49    inference(resolution,[],[f107,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f106])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f92,f120])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    v1_relat_1(sK2) | ~spl5_6),
% 0.22/0.49    inference(resolution,[],[f107,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f90,f80])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    v1_funct_1(sK2) | ~spl5_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f79])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl5_2),
% 0.22/0.49    inference(resolution,[],[f84,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    v2_funct_1(sK2) | ~spl5_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f83])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | (~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_10)),
% 0.22/0.49    inference(forward_demodulation,[],[f155,f126])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f93,f120])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f91,f80])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl5_2),
% 0.22/0.49    inference(resolution,[],[f84,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | (~spl5_4 | ~spl5_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f149,f100])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    ~v1_relat_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl5_10),
% 0.22/0.49    inference(resolution,[],[f146,f62])).
% 0.22/0.49  fof(f317,plain,(
% 0.22/0.49    spl5_35 | ~spl5_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f306,f161,f315])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    spl5_11 <=> v1_xboole_0(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.49  fof(f306,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | ~spl5_11),
% 0.22/0.49    inference(resolution,[],[f290,f70])).
% 0.22/0.49  fof(f290,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(X0) | sK2 = X0) ) | ~spl5_11),
% 0.22/0.49    inference(resolution,[],[f162,f48])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    v1_xboole_0(sK2) | ~spl5_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f161])).
% 0.22/0.49  fof(f289,plain,(
% 0.22/0.49    spl5_11 | ~spl5_23 | ~spl5_27),
% 0.22/0.49    inference(avatar_split_clause,[],[f288,f250,f216,f161])).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    spl5_23 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.49  fof(f288,plain,(
% 0.22/0.49    v1_xboole_0(sK2) | (~spl5_23 | ~spl5_27)),
% 0.22/0.49    inference(subsumption_resolution,[],[f287,f70])).
% 0.22/0.49  fof(f287,plain,(
% 0.22/0.49    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK2) | (~spl5_23 | ~spl5_27)),
% 0.22/0.49    inference(forward_demodulation,[],[f233,f251])).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    ~v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~spl5_23),
% 0.22/0.49    inference(resolution,[],[f217,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.22/0.49  fof(f217,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl5_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f216])).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    spl5_26 | spl5_27 | ~spl5_3 | ~spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f123,f106,f95,f250,f247])).
% 0.22/0.49  fof(f247,plain,(
% 0.22/0.49    spl5_26 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl5_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl5_3 | ~spl5_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f118,f96])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    v1_funct_2(sK2,sK0,sK1) | ~spl5_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f95])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl5_6),
% 0.22/0.49    inference(resolution,[],[f107,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    spl5_24 | ~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f154,f145,f110,f106,f99,f83,f79,f228])).
% 0.22/0.49  fof(f228,plain,(
% 0.22/0.49    spl5_24 <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_10)),
% 0.22/0.49    inference(forward_demodulation,[],[f153,f128])).
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | ~spl5_10)),
% 0.22/0.49    inference(forward_demodulation,[],[f152,f126])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | (~spl5_4 | ~spl5_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f148,f100])).
% 0.22/0.49  fof(f148,plain,(
% 0.22/0.49    ~v1_relat_1(k2_funct_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl5_10),
% 0.22/0.49    inference(resolution,[],[f146,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f34])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    spl5_23 | ~spl5_1 | ~spl5_6 | ~spl5_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f132,f110,f106,f79,f216])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | (~spl5_1 | ~spl5_6 | ~spl5_7)),
% 0.22/0.49    inference(forward_demodulation,[],[f131,f122])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl5_1 | ~spl5_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f87,f120])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl5_1),
% 0.22/0.49    inference(resolution,[],[f80,f62])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    spl5_22 | ~spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f119,f106,f212])).
% 0.22/0.49  fof(f212,plain,(
% 0.22/0.49    spl5_22 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl5_6),
% 0.22/0.49    inference(resolution,[],[f107,f63])).
% 0.22/0.49  fof(f202,plain,(
% 0.22/0.49    spl5_19 | ~spl5_1 | ~spl5_2 | ~spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f126,f106,f83,f79,f200])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    spl5_15 | ~spl5_1 | ~spl5_2 | ~spl5_6 | ~spl5_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f128,f110,f106,f83,f79,f176])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    spl5_10 | ~spl5_1 | ~spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f129,f106,f79,f145])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    v1_funct_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f89,f120])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl5_1),
% 0.22/0.49    inference(resolution,[],[f80,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    ~spl5_8 | ~spl5_9 | ~spl5_1 | ~spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f130,f106,f79,f141,f138])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_1 | ~spl5_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f38,f129])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  % (14210)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.49    inference(negated_conjecture,[],[f17])).
% 0.22/0.49  fof(f17,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    spl5_5 | ~spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f120,f106,f102])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl5_5 <=> v1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    spl5_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f43,f110])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f41,f106])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl5_4 | ~spl5_5 | ~spl5_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f88,f79,f102,f99])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~spl5_1),
% 0.22/0.49    inference(resolution,[],[f80,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    spl5_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f40,f95])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl5_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f83])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    v2_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    spl5_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f39,f79])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    v1_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (14206)------------------------------
% 0.22/0.49  % (14206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (14206)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (14206)Memory used [KB]: 6652
% 0.22/0.49  % (14206)Time elapsed: 0.063 s
% 0.22/0.49  % (14206)------------------------------
% 0.22/0.49  % (14206)------------------------------
% 0.22/0.50  % (14205)Success in time 0.127 s
%------------------------------------------------------------------------------
