%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:32 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 335 expanded)
%              Number of leaves         :   47 ( 133 expanded)
%              Depth                    :   13
%              Number of atoms          :  695 (1406 expanded)
%              Number of equality atoms :   62 (  77 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f747,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f136,f141,f146,f151,f156,f161,f166,f171,f176,f194,f214,f219,f240,f259,f281,f505,f539,f563,f587,f594,f601,f629,f675,f746])).

fof(f746,plain,
    ( spl5_2
    | ~ spl5_15
    | ~ spl5_45 ),
    inference(avatar_contradiction_clause,[],[f745])).

fof(f745,plain,
    ( $false
    | spl5_2
    | ~ spl5_15
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f744,f213])).

fof(f213,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl5_15
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f744,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_2
    | ~ spl5_45 ),
    inference(subsumption_resolution,[],[f727,f135])).

fof(f135,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f727,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl5_45 ),
    inference(superposition,[],[f358,f655])).

fof(f655,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f653])).

fof(f653,plain,
    ( spl5_45
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f358,plain,(
    ! [X0] :
      ( v2_funct_2(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f354])).

fof(f354,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v2_funct_2(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f270,f122])).

fof(f122,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f270,plain,(
    ! [X2] :
      ( v5_relat_1(X2,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f110,f125])).

fof(f125,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f675,plain,
    ( spl5_45
    | ~ spl5_15
    | ~ spl5_23
    | ~ spl5_41 ),
    inference(avatar_split_clause,[],[f674,f626,f278,f211,f653])).

fof(f278,plain,
    ( spl5_23
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f626,plain,
    ( spl5_41
  <=> r1_tarski(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f674,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl5_15
    | ~ spl5_23
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f673,f280])).

fof(f280,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f278])).

fof(f673,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ v5_relat_1(sK3,sK0)
    | ~ spl5_15
    | ~ spl5_41 ),
    inference(subsumption_resolution,[],[f669,f213])).

fof(f669,plain,
    ( ~ v1_relat_1(sK3)
    | sK0 = k2_relat_1(sK3)
    | ~ v5_relat_1(sK3,sK0)
    | ~ spl5_41 ),
    inference(resolution,[],[f628,f265])).

fof(f265,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = X1
      | ~ v5_relat_1(X0,X1) ) ),
    inference(resolution,[],[f109,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f628,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f626])).

fof(f629,plain,
    ( spl5_41
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f624,f511,f216,f211,f626])).

fof(f216,plain,
    ( spl5_16
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f511,plain,
    ( spl5_38
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f624,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_38 ),
    inference(forward_demodulation,[],[f623,f108])).

fof(f108,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f623,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(sK3))
    | ~ spl5_15
    | ~ spl5_16
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f622,f218])).

fof(f218,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f216])).

fof(f622,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | ~ spl5_15
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f613,f213])).

fof(f613,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl5_38 ),
    inference(superposition,[],[f111,f513])).

fof(f513,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f511])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f601,plain,
    ( spl5_1
    | spl5_40
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f600,f502,f168,f163,f158,f153,f148,f143,f582,f129])).

fof(f129,plain,
    ( spl5_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f582,plain,
    ( spl5_40
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f143,plain,
    ( spl5_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f148,plain,
    ( spl5_5
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f153,plain,
    ( spl5_6
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f158,plain,
    ( spl5_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f163,plain,
    ( spl5_8
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f168,plain,
    ( spl5_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f502,plain,
    ( spl5_36
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f600,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f599,f170])).

fof(f170,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f168])).

fof(f599,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f598,f165])).

fof(f165,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f163])).

fof(f598,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f597,f160])).

fof(f160,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f158])).

fof(f597,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f596,f155])).

fof(f155,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f153])).

fof(f596,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f595,f150])).

fof(f150,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f148])).

fof(f595,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_4
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f573,f145])).

fof(f145,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f573,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f553,f89])).

fof(f89,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f553,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_36 ),
    inference(superposition,[],[f83,f504])).

fof(f504,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f502])).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f594,plain,
    ( spl5_1
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | spl5_1
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f589,f131])).

fof(f131,plain,
    ( ~ v2_funct_1(sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f589,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_20 ),
    inference(resolution,[],[f239,f199])).

fof(f199,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v2_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f198,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f198,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f87,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f87,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).

fof(f239,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl5_20
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f587,plain,
    ( k1_xboole_0 != sK0
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f563,plain,
    ( spl5_38
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f562,f502,f168,f158,f153,f143,f511])).

fof(f562,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f561,f170])).

fof(f561,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f560,f160])).

fof(f560,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f559,f155])).

fof(f559,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_4
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f551,f145])).

fof(f551,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_36 ),
    inference(superposition,[],[f96,f504])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f539,plain,
    ( ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | spl5_35 ),
    inference(avatar_contradiction_clause,[],[f538])).

fof(f538,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_9
    | spl5_35 ),
    inference(subsumption_resolution,[],[f537,f170])).

fof(f537,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | spl5_35 ),
    inference(subsumption_resolution,[],[f536,f160])).

fof(f536,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_4
    | ~ spl5_6
    | spl5_35 ),
    inference(subsumption_resolution,[],[f535,f155])).

fof(f535,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_4
    | spl5_35 ),
    inference(subsumption_resolution,[],[f532,f145])).

fof(f532,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl5_35 ),
    inference(resolution,[],[f500,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f500,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl5_35 ),
    inference(avatar_component_clause,[],[f498])).

fof(f498,plain,
    ( spl5_35
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f505,plain,
    ( ~ spl5_35
    | spl5_36
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f494,f191,f502,f498])).

fof(f191,plain,
    ( spl5_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f494,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_13 ),
    inference(resolution,[],[f326,f193])).

fof(f193,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f191])).

fof(f326,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f90,f197])).

fof(f197,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f92,f93])).

fof(f93,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f281,plain,
    ( spl5_23
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f274,f143,f278])).

fof(f274,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f112,f145])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f259,plain,
    ( ~ spl5_22
    | spl5_19 ),
    inference(avatar_split_clause,[],[f254,f233,f256])).

fof(f256,plain,
    ( spl5_22
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f233,plain,
    ( spl5_19
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f254,plain,
    ( ~ v1_xboole_0(sK0)
    | spl5_19 ),
    inference(resolution,[],[f235,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f235,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f233])).

fof(f240,plain,
    ( ~ spl5_19
    | spl5_20
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f221,f158,f237,f233])).

fof(f221,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl5_7 ),
    inference(resolution,[],[f98,f160])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f219,plain,
    ( spl5_16
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f208,f158,f216])).

fof(f208,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_7 ),
    inference(resolution,[],[f97,f160])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f214,plain,
    ( spl5_15
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f207,f143,f211])).

fof(f207,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_4 ),
    inference(resolution,[],[f97,f145])).

fof(f194,plain,
    ( spl5_13
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f189,f138,f191])).

fof(f138,plain,
    ( spl5_3
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f189,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f140,f93])).

fof(f140,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f138])).

fof(f176,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f118,f173])).

fof(f173,plain,
    ( spl5_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f118,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f171,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f73,f168])).

fof(f73,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f64,f63])).

fof(f63,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f166,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f74,f163])).

fof(f74,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f161,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f75,f158])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f65])).

fof(f156,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f76,f153])).

fof(f76,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f65])).

fof(f151,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f77,f148])).

fof(f77,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f146,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f78,f143])).

fof(f78,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f65])).

fof(f141,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f79,f138])).

fof(f79,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f65])).

fof(f136,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f80,f133,f129])).

fof(f80,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:21:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (14673)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (14692)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (14684)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (14686)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (14674)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (14682)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (14678)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (14685)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (14676)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (14677)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (14672)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (14682)Refutation not found, incomplete strategy% (14682)------------------------------
% 0.21/0.54  % (14682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14682)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14682)Memory used [KB]: 10874
% 0.21/0.54  % (14682)Time elapsed: 0.121 s
% 0.21/0.54  % (14682)------------------------------
% 0.21/0.54  % (14682)------------------------------
% 0.21/0.54  % (14683)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (14687)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (14688)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (14679)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (14694)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (14701)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (14675)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (14693)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (14698)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (14680)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (14681)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (14696)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (14695)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (14690)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (14699)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (14697)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (14691)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.57  % (14689)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.57  % (14688)Refutation not found, incomplete strategy% (14688)------------------------------
% 0.21/0.57  % (14688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (14700)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.57  % (14688)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (14688)Memory used [KB]: 10746
% 0.21/0.57  % (14688)Time elapsed: 0.155 s
% 0.21/0.57  % (14688)------------------------------
% 0.21/0.57  % (14688)------------------------------
% 1.52/0.58  % (14700)Refutation not found, incomplete strategy% (14700)------------------------------
% 1.52/0.58  % (14700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.58  % (14700)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.58  
% 1.52/0.58  % (14700)Memory used [KB]: 10874
% 1.52/0.58  % (14700)Time elapsed: 0.156 s
% 1.52/0.58  % (14700)------------------------------
% 1.52/0.58  % (14700)------------------------------
% 1.87/0.60  % (14693)Refutation found. Thanks to Tanya!
% 1.87/0.60  % SZS status Theorem for theBenchmark
% 1.87/0.62  % SZS output start Proof for theBenchmark
% 1.87/0.62  fof(f747,plain,(
% 1.87/0.62    $false),
% 1.87/0.62    inference(avatar_sat_refutation,[],[f136,f141,f146,f151,f156,f161,f166,f171,f176,f194,f214,f219,f240,f259,f281,f505,f539,f563,f587,f594,f601,f629,f675,f746])).
% 1.87/0.62  fof(f746,plain,(
% 1.87/0.62    spl5_2 | ~spl5_15 | ~spl5_45),
% 1.87/0.62    inference(avatar_contradiction_clause,[],[f745])).
% 1.87/0.62  fof(f745,plain,(
% 1.87/0.62    $false | (spl5_2 | ~spl5_15 | ~spl5_45)),
% 1.87/0.62    inference(subsumption_resolution,[],[f744,f213])).
% 1.87/0.62  fof(f213,plain,(
% 1.87/0.62    v1_relat_1(sK3) | ~spl5_15),
% 1.87/0.62    inference(avatar_component_clause,[],[f211])).
% 1.87/0.62  fof(f211,plain,(
% 1.87/0.62    spl5_15 <=> v1_relat_1(sK3)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.87/0.62  fof(f744,plain,(
% 1.87/0.62    ~v1_relat_1(sK3) | (spl5_2 | ~spl5_45)),
% 1.87/0.62    inference(subsumption_resolution,[],[f727,f135])).
% 1.87/0.62  fof(f135,plain,(
% 1.87/0.62    ~v2_funct_2(sK3,sK0) | spl5_2),
% 1.87/0.62    inference(avatar_component_clause,[],[f133])).
% 1.87/0.62  fof(f133,plain,(
% 1.87/0.62    spl5_2 <=> v2_funct_2(sK3,sK0)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.87/0.62  fof(f727,plain,(
% 1.87/0.62    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl5_45),
% 1.87/0.62    inference(superposition,[],[f358,f655])).
% 1.87/0.62  fof(f655,plain,(
% 1.87/0.62    sK0 = k2_relat_1(sK3) | ~spl5_45),
% 1.87/0.62    inference(avatar_component_clause,[],[f653])).
% 1.87/0.62  fof(f653,plain,(
% 1.87/0.62    spl5_45 <=> sK0 = k2_relat_1(sK3)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 1.87/0.62  fof(f358,plain,(
% 1.87/0.62    ( ! [X0] : (v2_funct_2(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(duplicate_literal_removal,[],[f354])).
% 1.87/0.62  fof(f354,plain,(
% 1.87/0.62    ( ! [X0] : (~v1_relat_1(X0) | v2_funct_2(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(resolution,[],[f270,f122])).
% 1.87/0.62  fof(f122,plain,(
% 1.87/0.62    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.87/0.62    inference(equality_resolution,[],[f82])).
% 1.87/0.62  fof(f82,plain,(
% 1.87/0.62    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f66])).
% 1.87/0.62  fof(f66,plain,(
% 1.87/0.62    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.87/0.62    inference(nnf_transformation,[],[f35])).
% 1.87/0.62  fof(f35,plain,(
% 1.87/0.62    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.87/0.62    inference(flattening,[],[f34])).
% 1.87/0.62  fof(f34,plain,(
% 1.87/0.62    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.87/0.62    inference(ennf_transformation,[],[f20])).
% 1.87/0.62  fof(f20,axiom,(
% 1.87/0.62    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.87/0.62  fof(f270,plain,(
% 1.87/0.62    ( ! [X2] : (v5_relat_1(X2,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.87/0.62    inference(resolution,[],[f110,f125])).
% 1.87/0.62  fof(f125,plain,(
% 1.87/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.87/0.62    inference(equality_resolution,[],[f103])).
% 1.87/0.62  fof(f103,plain,(
% 1.87/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.87/0.62    inference(cnf_transformation,[],[f69])).
% 1.87/0.62  fof(f69,plain,(
% 1.87/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.87/0.62    inference(flattening,[],[f68])).
% 1.87/0.62  fof(f68,plain,(
% 1.87/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.87/0.62    inference(nnf_transformation,[],[f4])).
% 1.87/0.62  fof(f4,axiom,(
% 1.87/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.87/0.62  fof(f110,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f70])).
% 1.87/0.62  fof(f70,plain,(
% 1.87/0.62    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.87/0.62    inference(nnf_transformation,[],[f54])).
% 1.87/0.62  fof(f54,plain,(
% 1.87/0.62    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.87/0.62    inference(ennf_transformation,[],[f9])).
% 1.87/0.62  fof(f9,axiom,(
% 1.87/0.62    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.87/0.62  fof(f675,plain,(
% 1.87/0.62    spl5_45 | ~spl5_15 | ~spl5_23 | ~spl5_41),
% 1.87/0.62    inference(avatar_split_clause,[],[f674,f626,f278,f211,f653])).
% 1.87/0.62  fof(f278,plain,(
% 1.87/0.62    spl5_23 <=> v5_relat_1(sK3,sK0)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.87/0.62  fof(f626,plain,(
% 1.87/0.62    spl5_41 <=> r1_tarski(sK0,k2_relat_1(sK3))),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 1.87/0.62  fof(f674,plain,(
% 1.87/0.62    sK0 = k2_relat_1(sK3) | (~spl5_15 | ~spl5_23 | ~spl5_41)),
% 1.87/0.62    inference(subsumption_resolution,[],[f673,f280])).
% 1.87/0.62  fof(f280,plain,(
% 1.87/0.62    v5_relat_1(sK3,sK0) | ~spl5_23),
% 1.87/0.62    inference(avatar_component_clause,[],[f278])).
% 1.87/0.62  fof(f673,plain,(
% 1.87/0.62    sK0 = k2_relat_1(sK3) | ~v5_relat_1(sK3,sK0) | (~spl5_15 | ~spl5_41)),
% 1.87/0.62    inference(subsumption_resolution,[],[f669,f213])).
% 1.87/0.62  fof(f669,plain,(
% 1.87/0.62    ~v1_relat_1(sK3) | sK0 = k2_relat_1(sK3) | ~v5_relat_1(sK3,sK0) | ~spl5_41),
% 1.87/0.62    inference(resolution,[],[f628,f265])).
% 1.87/0.62  fof(f265,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~r1_tarski(X1,k2_relat_1(X0)) | ~v1_relat_1(X0) | k2_relat_1(X0) = X1 | ~v5_relat_1(X0,X1)) )),
% 1.87/0.62    inference(resolution,[],[f109,f104])).
% 1.87/0.62  fof(f104,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f69])).
% 1.87/0.62  fof(f109,plain,(
% 1.87/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f70])).
% 1.87/0.62  fof(f628,plain,(
% 1.87/0.62    r1_tarski(sK0,k2_relat_1(sK3)) | ~spl5_41),
% 1.87/0.62    inference(avatar_component_clause,[],[f626])).
% 1.87/0.62  fof(f629,plain,(
% 1.87/0.62    spl5_41 | ~spl5_15 | ~spl5_16 | ~spl5_38),
% 1.87/0.62    inference(avatar_split_clause,[],[f624,f511,f216,f211,f626])).
% 1.87/0.62  fof(f216,plain,(
% 1.87/0.62    spl5_16 <=> v1_relat_1(sK2)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.87/0.62  fof(f511,plain,(
% 1.87/0.62    spl5_38 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 1.87/0.62  fof(f624,plain,(
% 1.87/0.62    r1_tarski(sK0,k2_relat_1(sK3)) | (~spl5_15 | ~spl5_16 | ~spl5_38)),
% 1.87/0.62    inference(forward_demodulation,[],[f623,f108])).
% 1.87/0.62  fof(f108,plain,(
% 1.87/0.62    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.87/0.62    inference(cnf_transformation,[],[f13])).
% 1.87/0.62  fof(f13,axiom,(
% 1.87/0.62    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.87/0.62  fof(f623,plain,(
% 1.87/0.62    r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(sK3)) | (~spl5_15 | ~spl5_16 | ~spl5_38)),
% 1.87/0.62    inference(subsumption_resolution,[],[f622,f218])).
% 1.87/0.62  fof(f218,plain,(
% 1.87/0.62    v1_relat_1(sK2) | ~spl5_16),
% 1.87/0.62    inference(avatar_component_clause,[],[f216])).
% 1.87/0.62  fof(f622,plain,(
% 1.87/0.62    r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(sK3)) | ~v1_relat_1(sK2) | (~spl5_15 | ~spl5_38)),
% 1.87/0.62    inference(subsumption_resolution,[],[f613,f213])).
% 1.87/0.62  fof(f613,plain,(
% 1.87/0.62    r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl5_38),
% 1.87/0.62    inference(superposition,[],[f111,f513])).
% 1.87/0.62  fof(f513,plain,(
% 1.87/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl5_38),
% 1.87/0.62    inference(avatar_component_clause,[],[f511])).
% 1.87/0.62  fof(f111,plain,(
% 1.87/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f55])).
% 1.87/0.62  fof(f55,plain,(
% 1.87/0.62    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f11])).
% 1.87/0.62  fof(f11,axiom,(
% 1.87/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.87/0.62  fof(f601,plain,(
% 1.87/0.62    spl5_1 | spl5_40 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_36),
% 1.87/0.62    inference(avatar_split_clause,[],[f600,f502,f168,f163,f158,f153,f148,f143,f582,f129])).
% 1.87/0.62  fof(f129,plain,(
% 1.87/0.62    spl5_1 <=> v2_funct_1(sK2)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.87/0.62  fof(f582,plain,(
% 1.87/0.62    spl5_40 <=> k1_xboole_0 = sK0),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 1.87/0.62  fof(f143,plain,(
% 1.87/0.62    spl5_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.87/0.62  fof(f148,plain,(
% 1.87/0.62    spl5_5 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.87/0.62  fof(f153,plain,(
% 1.87/0.62    spl5_6 <=> v1_funct_1(sK3)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.87/0.62  fof(f158,plain,(
% 1.87/0.62    spl5_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.87/0.62  fof(f163,plain,(
% 1.87/0.62    spl5_8 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.87/0.62  fof(f168,plain,(
% 1.87/0.62    spl5_9 <=> v1_funct_1(sK2)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.87/0.62  fof(f502,plain,(
% 1.87/0.62    spl5_36 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 1.87/0.62  fof(f600,plain,(
% 1.87/0.62    k1_xboole_0 = sK0 | v2_funct_1(sK2) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_9 | ~spl5_36)),
% 1.87/0.62    inference(subsumption_resolution,[],[f599,f170])).
% 1.87/0.62  fof(f170,plain,(
% 1.87/0.62    v1_funct_1(sK2) | ~spl5_9),
% 1.87/0.62    inference(avatar_component_clause,[],[f168])).
% 1.87/0.62  fof(f599,plain,(
% 1.87/0.62    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_8 | ~spl5_36)),
% 1.87/0.62    inference(subsumption_resolution,[],[f598,f165])).
% 1.87/0.62  fof(f165,plain,(
% 1.87/0.62    v1_funct_2(sK2,sK0,sK1) | ~spl5_8),
% 1.87/0.62    inference(avatar_component_clause,[],[f163])).
% 1.87/0.62  fof(f598,plain,(
% 1.87/0.62    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | ~spl5_36)),
% 1.87/0.62    inference(subsumption_resolution,[],[f597,f160])).
% 1.87/0.62  fof(f160,plain,(
% 1.87/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_7),
% 1.87/0.62    inference(avatar_component_clause,[],[f158])).
% 1.87/0.62  fof(f597,plain,(
% 1.87/0.62    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_36)),
% 1.87/0.62    inference(subsumption_resolution,[],[f596,f155])).
% 1.87/0.62  fof(f155,plain,(
% 1.87/0.62    v1_funct_1(sK3) | ~spl5_6),
% 1.87/0.62    inference(avatar_component_clause,[],[f153])).
% 1.87/0.62  fof(f596,plain,(
% 1.87/0.62    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl5_4 | ~spl5_5 | ~spl5_36)),
% 1.87/0.62    inference(subsumption_resolution,[],[f595,f150])).
% 1.87/0.62  fof(f150,plain,(
% 1.87/0.62    v1_funct_2(sK3,sK1,sK0) | ~spl5_5),
% 1.87/0.62    inference(avatar_component_clause,[],[f148])).
% 1.87/0.62  fof(f595,plain,(
% 1.87/0.62    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl5_4 | ~spl5_36)),
% 1.87/0.62    inference(subsumption_resolution,[],[f573,f145])).
% 1.87/0.62  fof(f145,plain,(
% 1.87/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_4),
% 1.87/0.62    inference(avatar_component_clause,[],[f143])).
% 1.87/0.62  fof(f573,plain,(
% 1.87/0.62    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl5_36),
% 1.87/0.62    inference(subsumption_resolution,[],[f553,f89])).
% 1.87/0.62  fof(f89,plain,(
% 1.87/0.62    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f16])).
% 1.87/0.62  fof(f16,axiom,(
% 1.87/0.62    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.87/0.62  fof(f553,plain,(
% 1.87/0.62    ~v2_funct_1(k6_relat_1(sK0)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl5_36),
% 1.87/0.62    inference(superposition,[],[f83,f504])).
% 1.87/0.62  fof(f504,plain,(
% 1.87/0.62    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl5_36),
% 1.87/0.62    inference(avatar_component_clause,[],[f502])).
% 1.87/0.62  fof(f83,plain,(
% 1.87/0.62    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f37])).
% 1.87/0.62  fof(f37,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.87/0.62    inference(flattening,[],[f36])).
% 1.87/0.62  fof(f36,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.87/0.62    inference(ennf_transformation,[],[f26])).
% 1.87/0.62  fof(f26,axiom,(
% 1.87/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 1.87/0.62  fof(f594,plain,(
% 1.87/0.62    spl5_1 | ~spl5_20),
% 1.87/0.62    inference(avatar_contradiction_clause,[],[f593])).
% 1.87/0.62  fof(f593,plain,(
% 1.87/0.62    $false | (spl5_1 | ~spl5_20)),
% 1.87/0.62    inference(subsumption_resolution,[],[f589,f131])).
% 1.87/0.62  fof(f131,plain,(
% 1.87/0.62    ~v2_funct_1(sK2) | spl5_1),
% 1.87/0.62    inference(avatar_component_clause,[],[f129])).
% 1.87/0.62  fof(f589,plain,(
% 1.87/0.62    v2_funct_1(sK2) | ~spl5_20),
% 1.87/0.62    inference(resolution,[],[f239,f199])).
% 1.87/0.62  fof(f199,plain,(
% 1.87/0.62    ( ! [X0] : (~v1_xboole_0(X0) | v2_funct_1(X0)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f198,f115])).
% 1.87/0.62  fof(f115,plain,(
% 1.87/0.62    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f59])).
% 1.87/0.62  fof(f59,plain,(
% 1.87/0.62    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f8])).
% 1.87/0.62  fof(f8,axiom,(
% 1.87/0.62    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.87/0.62  fof(f198,plain,(
% 1.87/0.62    ( ! [X0] : (v2_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.87/0.62    inference(subsumption_resolution,[],[f87,f100])).
% 1.87/0.62  fof(f100,plain,(
% 1.87/0.62    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f49])).
% 1.87/0.62  fof(f49,plain,(
% 1.87/0.62    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f14])).
% 1.87/0.62  fof(f14,axiom,(
% 1.87/0.62    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 1.87/0.62  fof(f87,plain,(
% 1.87/0.62    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f39])).
% 1.87/0.62  fof(f39,plain,(
% 1.87/0.62    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.87/0.62    inference(flattening,[],[f38])).
% 1.87/0.62  fof(f38,plain,(
% 1.87/0.62    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 1.87/0.62    inference(ennf_transformation,[],[f15])).
% 1.87/0.62  fof(f15,axiom,(
% 1.87/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0) & v1_xboole_0(X0)) => (v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_1)).
% 1.87/0.62  fof(f239,plain,(
% 1.87/0.62    v1_xboole_0(sK2) | ~spl5_20),
% 1.87/0.62    inference(avatar_component_clause,[],[f237])).
% 1.87/0.62  fof(f237,plain,(
% 1.87/0.62    spl5_20 <=> v1_xboole_0(sK2)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.87/0.62  fof(f587,plain,(
% 1.87/0.62    k1_xboole_0 != sK0 | v1_xboole_0(sK0) | ~v1_xboole_0(k1_xboole_0)),
% 1.87/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.87/0.62  fof(f563,plain,(
% 1.87/0.62    spl5_38 | ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_9 | ~spl5_36),
% 1.87/0.62    inference(avatar_split_clause,[],[f562,f502,f168,f158,f153,f143,f511])).
% 1.87/0.62  fof(f562,plain,(
% 1.87/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | (~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_9 | ~spl5_36)),
% 1.87/0.62    inference(subsumption_resolution,[],[f561,f170])).
% 1.87/0.62  fof(f561,plain,(
% 1.87/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_36)),
% 1.87/0.62    inference(subsumption_resolution,[],[f560,f160])).
% 1.87/0.62  fof(f560,plain,(
% 1.87/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl5_4 | ~spl5_6 | ~spl5_36)),
% 1.87/0.62    inference(subsumption_resolution,[],[f559,f155])).
% 1.87/0.62  fof(f559,plain,(
% 1.87/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl5_4 | ~spl5_36)),
% 1.87/0.62    inference(subsumption_resolution,[],[f551,f145])).
% 1.87/0.62  fof(f551,plain,(
% 1.87/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl5_36),
% 1.87/0.62    inference(superposition,[],[f96,f504])).
% 1.87/0.62  fof(f96,plain,(
% 1.87/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f45])).
% 1.87/0.62  fof(f45,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.87/0.62    inference(flattening,[],[f44])).
% 1.87/0.62  fof(f44,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.87/0.62    inference(ennf_transformation,[],[f24])).
% 1.87/0.62  fof(f24,axiom,(
% 1.87/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.87/0.62  fof(f539,plain,(
% 1.87/0.62    ~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_9 | spl5_35),
% 1.87/0.62    inference(avatar_contradiction_clause,[],[f538])).
% 1.87/0.62  fof(f538,plain,(
% 1.87/0.62    $false | (~spl5_4 | ~spl5_6 | ~spl5_7 | ~spl5_9 | spl5_35)),
% 1.87/0.62    inference(subsumption_resolution,[],[f537,f170])).
% 1.87/0.62  fof(f537,plain,(
% 1.87/0.62    ~v1_funct_1(sK2) | (~spl5_4 | ~spl5_6 | ~spl5_7 | spl5_35)),
% 1.87/0.62    inference(subsumption_resolution,[],[f536,f160])).
% 1.87/0.62  fof(f536,plain,(
% 1.87/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl5_4 | ~spl5_6 | spl5_35)),
% 1.87/0.62    inference(subsumption_resolution,[],[f535,f155])).
% 1.87/0.62  fof(f535,plain,(
% 1.87/0.62    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl5_4 | spl5_35)),
% 1.87/0.62    inference(subsumption_resolution,[],[f532,f145])).
% 1.87/0.62  fof(f532,plain,(
% 1.87/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl5_35),
% 1.87/0.62    inference(resolution,[],[f500,f95])).
% 1.87/0.62  fof(f95,plain,(
% 1.87/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f43])).
% 1.87/0.62  fof(f43,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.87/0.62    inference(flattening,[],[f42])).
% 1.87/0.62  fof(f42,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.87/0.62    inference(ennf_transformation,[],[f21])).
% 1.87/0.62  fof(f21,axiom,(
% 1.87/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.87/0.62  fof(f500,plain,(
% 1.87/0.62    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl5_35),
% 1.87/0.62    inference(avatar_component_clause,[],[f498])).
% 1.87/0.62  fof(f498,plain,(
% 1.87/0.62    spl5_35 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 1.87/0.62  fof(f505,plain,(
% 1.87/0.62    ~spl5_35 | spl5_36 | ~spl5_13),
% 1.87/0.62    inference(avatar_split_clause,[],[f494,f191,f502,f498])).
% 1.87/0.62  fof(f191,plain,(
% 1.87/0.62    spl5_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.87/0.62  fof(f494,plain,(
% 1.87/0.62    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl5_13),
% 1.87/0.62    inference(resolution,[],[f326,f193])).
% 1.87/0.62  fof(f193,plain,(
% 1.87/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl5_13),
% 1.87/0.62    inference(avatar_component_clause,[],[f191])).
% 1.87/0.62  fof(f326,plain,(
% 1.87/0.62    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.87/0.62    inference(resolution,[],[f90,f197])).
% 1.87/0.62  fof(f197,plain,(
% 1.87/0.62    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.87/0.62    inference(forward_demodulation,[],[f92,f93])).
% 1.87/0.62  fof(f93,plain,(
% 1.87/0.62    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f25])).
% 1.87/0.62  fof(f25,axiom,(
% 1.87/0.62    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.87/0.62  fof(f92,plain,(
% 1.87/0.62    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f30])).
% 1.87/0.62  fof(f30,plain,(
% 1.87/0.62    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.87/0.62    inference(pure_predicate_removal,[],[f22])).
% 1.87/0.62  fof(f22,axiom,(
% 1.87/0.62    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.87/0.62  fof(f90,plain,(
% 1.87/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.87/0.62    inference(cnf_transformation,[],[f67])).
% 1.87/0.62  fof(f67,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.62    inference(nnf_transformation,[],[f41])).
% 1.87/0.62  fof(f41,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.62    inference(flattening,[],[f40])).
% 1.87/0.62  fof(f40,plain,(
% 1.87/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.87/0.62    inference(ennf_transformation,[],[f19])).
% 1.87/0.62  fof(f19,axiom,(
% 1.87/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.87/0.62  fof(f281,plain,(
% 1.87/0.62    spl5_23 | ~spl5_4),
% 1.87/0.62    inference(avatar_split_clause,[],[f274,f143,f278])).
% 1.87/0.62  fof(f274,plain,(
% 1.87/0.62    v5_relat_1(sK3,sK0) | ~spl5_4),
% 1.87/0.62    inference(resolution,[],[f112,f145])).
% 1.87/0.62  fof(f112,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f56])).
% 1.87/0.62  fof(f56,plain,(
% 1.87/0.62    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.62    inference(ennf_transformation,[],[f31])).
% 1.87/0.62  fof(f31,plain,(
% 1.87/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.87/0.62    inference(pure_predicate_removal,[],[f18])).
% 1.87/0.62  fof(f18,axiom,(
% 1.87/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.87/0.62  fof(f259,plain,(
% 1.87/0.62    ~spl5_22 | spl5_19),
% 1.87/0.62    inference(avatar_split_clause,[],[f254,f233,f256])).
% 1.87/0.62  fof(f256,plain,(
% 1.87/0.62    spl5_22 <=> v1_xboole_0(sK0)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.87/0.62  fof(f233,plain,(
% 1.87/0.62    spl5_19 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.87/0.62  fof(f254,plain,(
% 1.87/0.62    ~v1_xboole_0(sK0) | spl5_19),
% 1.87/0.62    inference(resolution,[],[f235,f99])).
% 1.87/0.62  fof(f99,plain,(
% 1.87/0.62    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f48])).
% 1.87/0.62  fof(f48,plain,(
% 1.87/0.62    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f6])).
% 1.87/0.62  fof(f6,axiom,(
% 1.87/0.62    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 1.87/0.62  fof(f235,plain,(
% 1.87/0.62    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl5_19),
% 1.87/0.62    inference(avatar_component_clause,[],[f233])).
% 1.87/0.62  fof(f240,plain,(
% 1.87/0.62    ~spl5_19 | spl5_20 | ~spl5_7),
% 1.87/0.62    inference(avatar_split_clause,[],[f221,f158,f237,f233])).
% 1.87/0.62  fof(f221,plain,(
% 1.87/0.62    v1_xboole_0(sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl5_7),
% 1.87/0.62    inference(resolution,[],[f98,f160])).
% 1.87/0.62  fof(f98,plain,(
% 1.87/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f47])).
% 1.87/0.62  fof(f47,plain,(
% 1.87/0.62    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.87/0.62    inference(ennf_transformation,[],[f7])).
% 1.87/0.62  fof(f7,axiom,(
% 1.87/0.62    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.87/0.62  fof(f219,plain,(
% 1.87/0.62    spl5_16 | ~spl5_7),
% 1.87/0.62    inference(avatar_split_clause,[],[f208,f158,f216])).
% 1.87/0.62  fof(f208,plain,(
% 1.87/0.62    v1_relat_1(sK2) | ~spl5_7),
% 1.87/0.62    inference(resolution,[],[f97,f160])).
% 1.87/0.62  fof(f97,plain,(
% 1.87/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.87/0.62    inference(cnf_transformation,[],[f46])).
% 1.87/0.62  fof(f46,plain,(
% 1.87/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.87/0.62    inference(ennf_transformation,[],[f17])).
% 1.87/0.62  fof(f17,axiom,(
% 1.87/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.87/0.62  fof(f214,plain,(
% 1.87/0.62    spl5_15 | ~spl5_4),
% 1.87/0.62    inference(avatar_split_clause,[],[f207,f143,f211])).
% 1.87/0.62  fof(f207,plain,(
% 1.87/0.62    v1_relat_1(sK3) | ~spl5_4),
% 1.87/0.62    inference(resolution,[],[f97,f145])).
% 1.87/0.62  fof(f194,plain,(
% 1.87/0.62    spl5_13 | ~spl5_3),
% 1.87/0.62    inference(avatar_split_clause,[],[f189,f138,f191])).
% 1.87/0.62  fof(f138,plain,(
% 1.87/0.62    spl5_3 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.87/0.62  fof(f189,plain,(
% 1.87/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl5_3),
% 1.87/0.62    inference(backward_demodulation,[],[f140,f93])).
% 1.87/0.62  fof(f140,plain,(
% 1.87/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl5_3),
% 1.87/0.62    inference(avatar_component_clause,[],[f138])).
% 1.87/0.62  fof(f176,plain,(
% 1.87/0.62    spl5_10),
% 1.87/0.62    inference(avatar_split_clause,[],[f118,f173])).
% 1.87/0.62  fof(f173,plain,(
% 1.87/0.62    spl5_10 <=> v1_xboole_0(k1_xboole_0)),
% 1.87/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.87/0.62  fof(f118,plain,(
% 1.87/0.62    v1_xboole_0(k1_xboole_0)),
% 1.87/0.62    inference(cnf_transformation,[],[f2])).
% 1.87/0.62  fof(f2,axiom,(
% 1.87/0.62    v1_xboole_0(k1_xboole_0)),
% 1.87/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.87/0.62  fof(f171,plain,(
% 1.87/0.62    spl5_9),
% 1.87/0.62    inference(avatar_split_clause,[],[f73,f168])).
% 1.87/0.62  fof(f73,plain,(
% 1.87/0.62    v1_funct_1(sK2)),
% 1.87/0.62    inference(cnf_transformation,[],[f65])).
% 1.87/0.62  fof(f65,plain,(
% 1.87/0.62    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.87/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f64,f63])).
% 1.87/0.63  fof(f63,plain,(
% 1.87/0.63    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.87/0.63    introduced(choice_axiom,[])).
% 1.87/0.63  fof(f64,plain,(
% 1.87/0.63    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.87/0.63    introduced(choice_axiom,[])).
% 1.87/0.63  fof(f33,plain,(
% 1.87/0.63    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.87/0.63    inference(flattening,[],[f32])).
% 1.87/0.63  fof(f32,plain,(
% 1.87/0.63    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.87/0.63    inference(ennf_transformation,[],[f28])).
% 1.87/0.63  fof(f28,negated_conjecture,(
% 1.87/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.87/0.63    inference(negated_conjecture,[],[f27])).
% 1.87/0.63  fof(f27,conjecture,(
% 1.87/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.87/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.87/0.63  fof(f166,plain,(
% 1.87/0.63    spl5_8),
% 1.87/0.63    inference(avatar_split_clause,[],[f74,f163])).
% 1.87/0.63  fof(f74,plain,(
% 1.87/0.63    v1_funct_2(sK2,sK0,sK1)),
% 1.87/0.63    inference(cnf_transformation,[],[f65])).
% 1.87/0.63  fof(f161,plain,(
% 1.87/0.63    spl5_7),
% 1.87/0.63    inference(avatar_split_clause,[],[f75,f158])).
% 1.87/0.63  fof(f75,plain,(
% 1.87/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.87/0.63    inference(cnf_transformation,[],[f65])).
% 1.87/0.63  fof(f156,plain,(
% 1.87/0.63    spl5_6),
% 1.87/0.63    inference(avatar_split_clause,[],[f76,f153])).
% 1.87/0.63  fof(f76,plain,(
% 1.87/0.63    v1_funct_1(sK3)),
% 1.87/0.63    inference(cnf_transformation,[],[f65])).
% 1.87/0.63  fof(f151,plain,(
% 1.87/0.63    spl5_5),
% 1.87/0.63    inference(avatar_split_clause,[],[f77,f148])).
% 1.87/0.63  fof(f77,plain,(
% 1.87/0.63    v1_funct_2(sK3,sK1,sK0)),
% 1.87/0.63    inference(cnf_transformation,[],[f65])).
% 1.87/0.63  fof(f146,plain,(
% 1.87/0.63    spl5_4),
% 1.87/0.63    inference(avatar_split_clause,[],[f78,f143])).
% 1.87/0.63  fof(f78,plain,(
% 1.87/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.87/0.63    inference(cnf_transformation,[],[f65])).
% 1.87/0.63  fof(f141,plain,(
% 1.87/0.63    spl5_3),
% 1.87/0.63    inference(avatar_split_clause,[],[f79,f138])).
% 1.87/0.63  fof(f79,plain,(
% 1.87/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.87/0.63    inference(cnf_transformation,[],[f65])).
% 1.87/0.63  fof(f136,plain,(
% 1.87/0.63    ~spl5_1 | ~spl5_2),
% 1.87/0.63    inference(avatar_split_clause,[],[f80,f133,f129])).
% 1.87/0.63  fof(f80,plain,(
% 1.87/0.63    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.87/0.63    inference(cnf_transformation,[],[f65])).
% 1.87/0.63  % SZS output end Proof for theBenchmark
% 1.87/0.63  % (14693)------------------------------
% 1.87/0.63  % (14693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.63  % (14693)Termination reason: Refutation
% 1.87/0.63  
% 1.87/0.63  % (14693)Memory used [KB]: 6780
% 1.87/0.63  % (14693)Time elapsed: 0.182 s
% 1.87/0.63  % (14693)------------------------------
% 1.87/0.63  % (14693)------------------------------
% 1.87/0.63  % (14671)Success in time 0.266 s
%------------------------------------------------------------------------------
