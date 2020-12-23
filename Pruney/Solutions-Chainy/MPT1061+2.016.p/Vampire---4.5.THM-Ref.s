%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  245 ( 521 expanded)
%              Number of leaves         :   58 ( 216 expanded)
%              Depth                    :   11
%              Number of atoms          :  667 (1472 expanded)
%              Number of equality atoms :  114 ( 261 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f986,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f119,f132,f137,f155,f160,f213,f260,f311,f313,f424,f514,f594,f639,f662,f691,f693,f700,f716,f721,f722,f748,f749,f768,f807,f811,f825,f830,f872,f877,f919,f953,f958,f981,f985])).

fof(f985,plain,
    ( ~ spl5_12
    | ~ spl5_23
    | spl5_78 ),
    inference(avatar_contradiction_clause,[],[f983])).

fof(f983,plain,
    ( $false
    | ~ spl5_12
    | ~ spl5_23
    | spl5_78 ),
    inference(unit_resulting_resolution,[],[f147,f322,f980,f139])).

fof(f139,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f86,f84])).

fof(f84,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f86,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f980,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl5_78 ),
    inference(avatar_component_clause,[],[f978])).

fof(f978,plain,
    ( spl5_78
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f322,plain,
    ( ! [X2,X3] : k1_xboole_0 = k1_relset_1(X2,X3,k1_xboole_0)
    | ~ spl5_23 ),
    inference(backward_demodulation,[],[f272,f294])).

fof(f294,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl5_23
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f272,plain,(
    ! [X2,X3] : k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0) ),
    inference(resolution,[],[f253,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f253,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(resolution,[],[f69,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f147,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl5_12
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f981,plain,
    ( ~ spl5_78
    | ~ spl5_73
    | spl5_75 ),
    inference(avatar_split_clause,[],[f966,f950,f910,f978])).

fof(f910,plain,
    ( spl5_73
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f950,plain,
    ( spl5_75
  <=> v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f966,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_73
    | spl5_75 ),
    inference(backward_demodulation,[],[f952,f912])).

fof(f912,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f910])).

fof(f952,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | spl5_75 ),
    inference(avatar_component_clause,[],[f950])).

fof(f958,plain,
    ( spl5_73
    | ~ spl5_23
    | ~ spl5_42
    | ~ spl5_60
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f957,f916,f772,f606,f292,f910])).

fof(f606,plain,
    ( spl5_42
  <=> r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f772,plain,
    ( spl5_60
  <=> sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f916,plain,
    ( spl5_74
  <=> k1_xboole_0 = k7_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f957,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_23
    | ~ spl5_42
    | ~ spl5_60
    | ~ spl5_74 ),
    inference(forward_demodulation,[],[f936,f322])).

fof(f936,plain,
    ( ! [X4] : sK1 = k1_relset_1(X4,k1_xboole_0,k1_xboole_0)
    | ~ spl5_42
    | ~ spl5_60
    | ~ spl5_74 ),
    inference(backward_demodulation,[],[f914,f918])).

fof(f918,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK1)
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f916])).

fof(f914,plain,
    ( ! [X4] : sK1 = k1_relset_1(X4,k1_xboole_0,k7_relat_1(sK4,sK1))
    | ~ spl5_42
    | ~ spl5_60 ),
    inference(forward_demodulation,[],[f900,f773])).

fof(f773,plain,
    ( sK1 = k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f772])).

fof(f900,plain,
    ( ! [X4] : k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(X4,k1_xboole_0,k7_relat_1(sK4,sK1))
    | ~ spl5_42 ),
    inference(resolution,[],[f607,f261])).

fof(f261,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_relat_1(X0) = k1_relset_1(X1,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f254,f63])).

fof(f254,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_relat_1(X1) = k1_relset_1(X0,k1_xboole_0,X1) ) ),
    inference(superposition,[],[f69,f83])).

fof(f83,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f607,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0)
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f606])).

fof(f953,plain,
    ( ~ spl5_75
    | spl5_65
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f933,f916,f827,f950])).

fof(f827,plain,
    ( spl5_65
  <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

% (8930)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f933,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | spl5_65
    | ~ spl5_74 ),
    inference(backward_demodulation,[],[f829,f918])).

fof(f829,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0)
    | spl5_65 ),
    inference(avatar_component_clause,[],[f827])).

fof(f919,plain,
    ( spl5_74
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f901,f606,f916])).

fof(f901,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK1)
    | ~ spl5_42 ),
    inference(resolution,[],[f607,f180])).

fof(f180,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f62,f52])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f877,plain,
    ( ~ spl5_59
    | spl5_71 ),
    inference(avatar_contradiction_clause,[],[f874])).

fof(f874,plain,
    ( $false
    | ~ spl5_59
    | spl5_71 ),
    inference(unit_resulting_resolution,[],[f767,f871])).

fof(f871,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | spl5_71 ),
    inference(avatar_component_clause,[],[f869])).

fof(f869,plain,
    ( spl5_71
  <=> v1_funct_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f767,plain,
    ( ! [X1] : v1_funct_1(k7_relat_1(sK4,X1))
    | ~ spl5_59 ),
    inference(avatar_component_clause,[],[f766])).

fof(f766,plain,
    ( spl5_59
  <=> ! [X1] : v1_funct_1(k7_relat_1(sK4,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f872,plain,
    ( ~ spl5_71
    | ~ spl5_4
    | ~ spl5_6
    | spl5_9 ),
    inference(avatar_split_clause,[],[f867,f129,f116,f106,f869])).

fof(f106,plain,
    ( spl5_4
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f116,plain,
    ( spl5_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f129,plain,
    ( spl5_9
  <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f867,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | spl5_9 ),
    inference(forward_demodulation,[],[f131,f558])).

fof(f558,plain,
    ( ! [X0] : k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(resolution,[],[f480,f108])).

fof(f108,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f480,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) )
    | ~ spl5_6 ),
    inference(resolution,[],[f78,f118])).

fof(f118,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f131,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f830,plain,
    ( ~ spl5_65
    | spl5_51
    | ~ spl5_53 ),
    inference(avatar_split_clause,[],[f815,f713,f697,f827])).

fof(f697,plain,
    ( spl5_51
  <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f713,plain,
    ( spl5_53
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f815,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0)
    | spl5_51
    | ~ spl5_53 ),
    inference(backward_demodulation,[],[f699,f715])).

fof(f715,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f713])).

fof(f699,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl5_51 ),
    inference(avatar_component_clause,[],[f697])).

fof(f825,plain,
    ( spl5_42
    | ~ spl5_38
    | ~ spl5_53 ),
    inference(avatar_split_clause,[],[f824,f713,f586,f606])).

fof(f586,plain,
    ( spl5_38
  <=> r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f824,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0)
    | ~ spl5_38
    | ~ spl5_53 ),
    inference(forward_demodulation,[],[f814,f83])).

fof(f814,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k1_xboole_0))
    | ~ spl5_38
    | ~ spl5_53 ),
    inference(backward_demodulation,[],[f587,f715])).

fof(f587,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f586])).

fof(f811,plain,
    ( spl5_52
    | ~ spl5_54
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f808,f772,f718,f709])).

fof(f709,plain,
    ( spl5_52
  <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f718,plain,
    ( spl5_54
  <=> k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f808,plain,
    ( sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_54
    | ~ spl5_60 ),
    inference(backward_demodulation,[],[f720,f773])).

fof(f720,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f718])).

fof(f807,plain,
    ( spl5_60
    | ~ spl5_3
    | ~ spl5_44
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f800,f745,f618,f101,f772])).

fof(f101,plain,
    ( spl5_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f618,plain,
    ( spl5_44
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f745,plain,
    ( spl5_56
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f800,plain,
    ( sK1 = k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_3
    | ~ spl5_44
    | ~ spl5_56 ),
    inference(resolution,[],[f750,f103])).

fof(f103,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f750,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK0)
        | k1_relat_1(k7_relat_1(sK4,X1)) = X1 )
    | ~ spl5_44
    | ~ spl5_56 ),
    inference(backward_demodulation,[],[f641,f747])).

fof(f747,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f745])).

fof(f641,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_relat_1(sK4))
        | k1_relat_1(k7_relat_1(sK4,X1)) = X1 )
    | ~ spl5_44 ),
    inference(resolution,[],[f619,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f619,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f618])).

fof(f768,plain,
    ( ~ spl5_6
    | ~ spl5_4
    | spl5_59
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f760,f116,f106,f766,f106,f116])).

fof(f760,plain,
    ( ! [X1] :
        ( v1_funct_1(k7_relat_1(sK4,X1))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
        | ~ v1_funct_1(sK4) )
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(superposition,[],[f79,f558])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f749,plain,
    ( k1_xboole_0 != sK3
    | v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f748,plain,
    ( ~ spl5_5
    | spl5_55
    | spl5_56
    | ~ spl5_4
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f739,f257,f106,f745,f741,f111])).

fof(f111,plain,
    ( spl5_5
  <=> v1_funct_2(sK4,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f741,plain,
    ( spl5_55
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f257,plain,
    ( spl5_21
  <=> k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f739,plain,
    ( sK0 = k1_relat_1(sK4)
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK4,sK0,sK3)
    | ~ spl5_4
    | ~ spl5_21 ),
    inference(forward_demodulation,[],[f736,f259])).

fof(f259,plain,
    ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f257])).

fof(f736,plain,
    ( k1_xboole_0 = sK3
    | sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ v1_funct_2(sK4,sK0,sK3)
    | ~ spl5_4 ),
    inference(resolution,[],[f76,f108])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f722,plain,
    ( spl5_38
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f707,f581,f586])).

fof(f581,plain,
    ( spl5_37
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f707,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ spl5_37 ),
    inference(resolution,[],[f582,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f582,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f581])).

% (8938)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f721,plain,
    ( spl5_54
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f706,f581,f718])).

fof(f706,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl5_37 ),
    inference(resolution,[],[f582,f69])).

fof(f716,plain,
    ( spl5_51
    | ~ spl5_52
    | spl5_53
    | ~ spl5_37 ),
    inference(avatar_split_clause,[],[f703,f581,f713,f709,f697])).

fof(f703,plain,
    ( k1_xboole_0 = sK2
    | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl5_37 ),
    inference(resolution,[],[f582,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f700,plain,
    ( ~ spl5_51
    | ~ spl5_4
    | ~ spl5_6
    | spl5_8 ),
    inference(avatar_split_clause,[],[f695,f125,f116,f106,f697])).

fof(f125,plain,
    ( spl5_8
  <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f695,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ spl5_4
    | ~ spl5_6
    | spl5_8 ),
    inference(forward_demodulation,[],[f127,f558])).

fof(f127,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f693,plain,
    ( ~ spl5_39
    | ~ spl5_49
    | ~ spl5_28
    | spl5_37
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f692,f618,f581,f421,f659,f591])).

fof(f591,plain,
    ( spl5_39
  <=> v1_relat_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f659,plain,
    ( spl5_49
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f421,plain,
    ( spl5_28
  <=> r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f692,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl5_37
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f668,f640])).

fof(f640,plain,
    ( ! [X0] : k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0))
    | ~ spl5_44 ),
    inference(resolution,[],[f619,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f668,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | spl5_37 ),
    inference(resolution,[],[f583,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f583,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_37 ),
    inference(avatar_component_clause,[],[f581])).

fof(f691,plain,
    ( ~ spl5_44
    | spl5_49 ),
    inference(avatar_split_clause,[],[f689,f659,f618])).

fof(f689,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_49 ),
    inference(resolution,[],[f661,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f661,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | spl5_49 ),
    inference(avatar_component_clause,[],[f659])).

fof(f662,plain,
    ( ~ spl5_49
    | ~ spl5_28
    | ~ spl5_39
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f657,f618,f121,f116,f106,f591,f421,f659])).

fof(f121,plain,
    ( spl5_7
  <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f657,plain,
    ( ~ v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f656,f558])).

fof(f656,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f655,f640])).

fof(f655,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7 ),
    inference(forward_demodulation,[],[f654,f558])).

fof(f654,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7 ),
    inference(forward_demodulation,[],[f542,f558])).

fof(f542,plain,
    ( ~ r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2)
    | ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_7 ),
    inference(resolution,[],[f123,f68])).

fof(f123,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f639,plain,
    ( ~ spl5_4
    | spl5_44 ),
    inference(avatar_contradiction_clause,[],[f637])).

fof(f637,plain,
    ( $false
    | ~ spl5_4
    | spl5_44 ),
    inference(unit_resulting_resolution,[],[f54,f108,f620,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f620,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_44 ),
    inference(avatar_component_clause,[],[f618])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f594,plain,
    ( spl5_39
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f565,f446,f116,f106,f591])).

fof(f446,plain,
    ( spl5_29
  <=> v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f565,plain,
    ( v1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_29 ),
    inference(backward_demodulation,[],[f447,f558])).

fof(f447,plain,
    ( v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f446])).

fof(f514,plain,
    ( ~ spl5_6
    | ~ spl5_4
    | spl5_29 ),
    inference(avatar_split_clause,[],[f505,f446,f106,f116])).

fof(f505,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | ~ v1_funct_1(sK4)
    | spl5_29 ),
    inference(resolution,[],[f80,f461])).

fof(f461,plain,
    ( ! [X2,X3] : ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | spl5_29 ),
    inference(resolution,[],[f458,f54])).

fof(f458,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(X0)) )
    | spl5_29 ),
    inference(resolution,[],[f448,f53])).

fof(f448,plain,
    ( ~ v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | spl5_29 ),
    inference(avatar_component_clause,[],[f446])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f424,plain,
    ( spl5_28
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f419,f106,f96,f421])).

fof(f96,plain,
    ( spl5_2
  <=> r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f419,plain,
    ( r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f98,f415])).

fof(f415,plain,
    ( ! [X0] : k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0)
    | ~ spl5_4 ),
    inference(resolution,[],[f77,f108])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f98,plain,
    ( r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f313,plain,
    ( spl5_23
    | ~ spl5_19
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f312,f308,f210,f292])).

fof(f210,plain,
    ( spl5_19
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f308,plain,
    ( spl5_25
  <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f312,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_19
    | ~ spl5_25 ),
    inference(backward_demodulation,[],[f212,f310])).

fof(f310,plain,
    ( k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f308])).

fof(f212,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f210])).

fof(f311,plain,
    ( spl5_25
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f302,f152,f146,f308])).

fof(f152,plain,
    ( spl5_13
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f302,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl5_13 ),
    inference(superposition,[],[f226,f84])).

fof(f226,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) )
    | ~ spl5_13 ),
    inference(resolution,[],[f223,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f223,plain,
    ( ! [X3] :
        ( ~ v4_relat_1(k1_xboole_0,X3)
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X3) )
    | ~ spl5_13 ),
    inference(resolution,[],[f59,f154])).

fof(f154,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f152])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f260,plain,
    ( spl5_21
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f252,f106,f257])).

fof(f252,plain,
    ( k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)
    | ~ spl5_4 ),
    inference(resolution,[],[f69,f108])).

fof(f213,plain,
    ( spl5_19
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f206,f152,f210])).

fof(f206,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl5_13 ),
    inference(resolution,[],[f204,f154])).

fof(f204,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f180,f56])).

fof(f160,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f52,f148,f63])).

fof(f148,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f155,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f150,f152])).

fof(f150,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f54,f83])).

fof(f137,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f51,f134])).

fof(f134,plain,
    ( spl5_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f132,plain,
    ( ~ spl5_7
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f44,f129,f125,f121])).

fof(f44,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

fof(f119,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f45,f116])).

fof(f45,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f114,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f46,f111])).

fof(f46,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f109,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f47,f106])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f24])).

fof(f104,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f48,f101])).

fof(f48,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f49,f96])).

fof(f49,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f94,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f50,f91])).

fof(f91,plain,
    ( spl5_1
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f50,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (8937)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (8945)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (8922)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (8927)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (8925)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (8926)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % (8928)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (8940)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.53  % (8923)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (8939)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.54  % (8935)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (8933)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.54  % (8929)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.54  % (8941)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.54  % (8934)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.54  % (8931)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.54  % (8946)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.55  % (8936)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.55  % (8944)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.55  % (8947)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.56  % (8924)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.57  % (8932)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.57  % (8943)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.57  % (8937)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.58  % (8942)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f986,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f119,f132,f137,f155,f160,f213,f260,f311,f313,f424,f514,f594,f639,f662,f691,f693,f700,f716,f721,f722,f748,f749,f768,f807,f811,f825,f830,f872,f877,f919,f953,f958,f981,f985])).
% 0.20/0.59  fof(f985,plain,(
% 0.20/0.59    ~spl5_12 | ~spl5_23 | spl5_78),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f983])).
% 0.20/0.59  fof(f983,plain,(
% 0.20/0.59    $false | (~spl5_12 | ~spl5_23 | spl5_78)),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f147,f322,f980,f139])).
% 0.20/0.59  fof(f139,plain,(
% 0.20/0.59    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.59    inference(forward_demodulation,[],[f86,f84])).
% 0.20/0.59  fof(f84,plain,(
% 0.20/0.59    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.59    inference(equality_resolution,[],[f66])).
% 0.20/0.59  fof(f66,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f4])).
% 0.20/0.59  fof(f4,axiom,(
% 0.20/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.59  fof(f86,plain,(
% 0.20/0.59    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.59    inference(equality_resolution,[],[f73])).
% 0.20/0.59  fof(f73,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f38])).
% 0.20/0.59  fof(f38,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.59    inference(flattening,[],[f37])).
% 0.20/0.59  fof(f37,plain,(
% 0.20/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.59    inference(ennf_transformation,[],[f17])).
% 0.20/0.59  fof(f17,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.59  fof(f980,plain,(
% 0.20/0.59    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl5_78),
% 0.20/0.59    inference(avatar_component_clause,[],[f978])).
% 0.20/0.59  fof(f978,plain,(
% 0.20/0.59    spl5_78 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 0.20/0.59  fof(f322,plain,(
% 0.20/0.59    ( ! [X2,X3] : (k1_xboole_0 = k1_relset_1(X2,X3,k1_xboole_0)) ) | ~spl5_23),
% 0.20/0.59    inference(backward_demodulation,[],[f272,f294])).
% 0.20/0.59  fof(f294,plain,(
% 0.20/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_23),
% 0.20/0.59    inference(avatar_component_clause,[],[f292])).
% 0.20/0.59  fof(f292,plain,(
% 0.20/0.59    spl5_23 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.20/0.59  fof(f272,plain,(
% 0.20/0.59    ( ! [X2,X3] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0)) )),
% 0.20/0.59    inference(resolution,[],[f253,f52])).
% 0.20/0.59  fof(f52,plain,(
% 0.20/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.59  fof(f253,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_zfmisc_1(X0,X1)) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.59    inference(resolution,[],[f69,f63])).
% 0.20/0.59  fof(f63,plain,(
% 0.20/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f5])).
% 0.20/0.59  fof(f5,axiom,(
% 0.20/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.59  fof(f69,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f35])).
% 0.20/0.59  fof(f35,plain,(
% 0.20/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.59    inference(ennf_transformation,[],[f14])).
% 0.20/0.59  fof(f14,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.59  fof(f147,plain,(
% 0.20/0.59    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl5_12),
% 0.20/0.59    inference(avatar_component_clause,[],[f146])).
% 0.20/0.59  fof(f146,plain,(
% 0.20/0.59    spl5_12 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.59  fof(f981,plain,(
% 0.20/0.59    ~spl5_78 | ~spl5_73 | spl5_75),
% 0.20/0.59    inference(avatar_split_clause,[],[f966,f950,f910,f978])).
% 0.20/0.59  fof(f910,plain,(
% 0.20/0.59    spl5_73 <=> k1_xboole_0 = sK1),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 0.20/0.59  fof(f950,plain,(
% 0.20/0.59    spl5_75 <=> v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 0.20/0.59  fof(f966,plain,(
% 0.20/0.59    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl5_73 | spl5_75)),
% 0.20/0.59    inference(backward_demodulation,[],[f952,f912])).
% 0.20/0.59  fof(f912,plain,(
% 0.20/0.59    k1_xboole_0 = sK1 | ~spl5_73),
% 0.20/0.59    inference(avatar_component_clause,[],[f910])).
% 0.20/0.59  fof(f952,plain,(
% 0.20/0.59    ~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | spl5_75),
% 0.20/0.59    inference(avatar_component_clause,[],[f950])).
% 0.20/0.59  fof(f958,plain,(
% 0.20/0.59    spl5_73 | ~spl5_23 | ~spl5_42 | ~spl5_60 | ~spl5_74),
% 0.20/0.59    inference(avatar_split_clause,[],[f957,f916,f772,f606,f292,f910])).
% 0.20/0.59  fof(f606,plain,(
% 0.20/0.59    spl5_42 <=> r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.20/0.59  fof(f772,plain,(
% 0.20/0.59    spl5_60 <=> sK1 = k1_relat_1(k7_relat_1(sK4,sK1))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 0.20/0.59  fof(f916,plain,(
% 0.20/0.59    spl5_74 <=> k1_xboole_0 = k7_relat_1(sK4,sK1)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 0.20/0.59  fof(f957,plain,(
% 0.20/0.59    k1_xboole_0 = sK1 | (~spl5_23 | ~spl5_42 | ~spl5_60 | ~spl5_74)),
% 0.20/0.59    inference(forward_demodulation,[],[f936,f322])).
% 0.20/0.59  fof(f936,plain,(
% 0.20/0.59    ( ! [X4] : (sK1 = k1_relset_1(X4,k1_xboole_0,k1_xboole_0)) ) | (~spl5_42 | ~spl5_60 | ~spl5_74)),
% 0.20/0.59    inference(backward_demodulation,[],[f914,f918])).
% 0.20/0.59  fof(f918,plain,(
% 0.20/0.59    k1_xboole_0 = k7_relat_1(sK4,sK1) | ~spl5_74),
% 0.20/0.59    inference(avatar_component_clause,[],[f916])).
% 0.20/0.59  fof(f914,plain,(
% 0.20/0.59    ( ! [X4] : (sK1 = k1_relset_1(X4,k1_xboole_0,k7_relat_1(sK4,sK1))) ) | (~spl5_42 | ~spl5_60)),
% 0.20/0.59    inference(forward_demodulation,[],[f900,f773])).
% 0.20/0.59  fof(f773,plain,(
% 0.20/0.59    sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) | ~spl5_60),
% 0.20/0.59    inference(avatar_component_clause,[],[f772])).
% 0.20/0.59  fof(f900,plain,(
% 0.20/0.59    ( ! [X4] : (k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(X4,k1_xboole_0,k7_relat_1(sK4,sK1))) ) | ~spl5_42),
% 0.20/0.59    inference(resolution,[],[f607,f261])).
% 0.20/0.59  fof(f261,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | k1_relat_1(X0) = k1_relset_1(X1,k1_xboole_0,X0)) )),
% 0.20/0.59    inference(resolution,[],[f254,f63])).
% 0.20/0.59  fof(f254,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_relat_1(X1) = k1_relset_1(X0,k1_xboole_0,X1)) )),
% 0.20/0.59    inference(superposition,[],[f69,f83])).
% 0.20/0.59  fof(f83,plain,(
% 0.20/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.59    inference(equality_resolution,[],[f67])).
% 0.20/0.59  fof(f67,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f4])).
% 0.20/0.59  fof(f607,plain,(
% 0.20/0.59    r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0) | ~spl5_42),
% 0.20/0.59    inference(avatar_component_clause,[],[f606])).
% 0.20/0.59  fof(f953,plain,(
% 0.20/0.59    ~spl5_75 | spl5_65 | ~spl5_74),
% 0.20/0.59    inference(avatar_split_clause,[],[f933,f916,f827,f950])).
% 0.20/0.59  fof(f827,plain,(
% 0.20/0.59    spl5_65 <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 0.20/0.60  % (8930)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.60  fof(f933,plain,(
% 0.20/0.60    ~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | (spl5_65 | ~spl5_74)),
% 0.20/0.60    inference(backward_demodulation,[],[f829,f918])).
% 0.20/0.60  fof(f829,plain,(
% 0.20/0.60    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0) | spl5_65),
% 0.20/0.60    inference(avatar_component_clause,[],[f827])).
% 0.20/0.60  fof(f919,plain,(
% 0.20/0.60    spl5_74 | ~spl5_42),
% 0.20/0.60    inference(avatar_split_clause,[],[f901,f606,f916])).
% 0.20/0.60  fof(f901,plain,(
% 0.20/0.60    k1_xboole_0 = k7_relat_1(sK4,sK1) | ~spl5_42),
% 0.20/0.60    inference(resolution,[],[f607,f180])).
% 0.20/0.60  fof(f180,plain,(
% 0.20/0.60    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.20/0.60    inference(resolution,[],[f62,f52])).
% 0.20/0.60  fof(f62,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.60    inference(cnf_transformation,[],[f2])).
% 0.20/0.60  fof(f2,axiom,(
% 0.20/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.60  fof(f877,plain,(
% 0.20/0.60    ~spl5_59 | spl5_71),
% 0.20/0.60    inference(avatar_contradiction_clause,[],[f874])).
% 0.20/0.60  fof(f874,plain,(
% 0.20/0.60    $false | (~spl5_59 | spl5_71)),
% 0.20/0.60    inference(unit_resulting_resolution,[],[f767,f871])).
% 0.20/0.60  fof(f871,plain,(
% 0.20/0.60    ~v1_funct_1(k7_relat_1(sK4,sK1)) | spl5_71),
% 0.20/0.60    inference(avatar_component_clause,[],[f869])).
% 0.20/0.60  fof(f869,plain,(
% 0.20/0.60    spl5_71 <=> v1_funct_1(k7_relat_1(sK4,sK1))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 0.20/0.60  fof(f767,plain,(
% 0.20/0.60    ( ! [X1] : (v1_funct_1(k7_relat_1(sK4,X1))) ) | ~spl5_59),
% 0.20/0.60    inference(avatar_component_clause,[],[f766])).
% 0.20/0.60  fof(f766,plain,(
% 0.20/0.60    spl5_59 <=> ! [X1] : v1_funct_1(k7_relat_1(sK4,X1))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 0.20/0.60  fof(f872,plain,(
% 0.20/0.60    ~spl5_71 | ~spl5_4 | ~spl5_6 | spl5_9),
% 0.20/0.60    inference(avatar_split_clause,[],[f867,f129,f116,f106,f869])).
% 0.20/0.60  fof(f106,plain,(
% 0.20/0.60    spl5_4 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.60  fof(f116,plain,(
% 0.20/0.60    spl5_6 <=> v1_funct_1(sK4)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.60  fof(f129,plain,(
% 0.20/0.60    spl5_9 <=> v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.60  fof(f867,plain,(
% 0.20/0.60    ~v1_funct_1(k7_relat_1(sK4,sK1)) | (~spl5_4 | ~spl5_6 | spl5_9)),
% 0.20/0.60    inference(forward_demodulation,[],[f131,f558])).
% 0.20/0.60  fof(f558,plain,(
% 0.20/0.60    ( ! [X0] : (k2_partfun1(sK0,sK3,sK4,X0) = k7_relat_1(sK4,X0)) ) | (~spl5_4 | ~spl5_6)),
% 0.20/0.60    inference(resolution,[],[f480,f108])).
% 0.20/0.60  fof(f108,plain,(
% 0.20/0.60    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~spl5_4),
% 0.20/0.60    inference(avatar_component_clause,[],[f106])).
% 0.20/0.60  fof(f480,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)) ) | ~spl5_6),
% 0.20/0.60    inference(resolution,[],[f78,f118])).
% 0.20/0.60  fof(f118,plain,(
% 0.20/0.60    v1_funct_1(sK4) | ~spl5_6),
% 0.20/0.60    inference(avatar_component_clause,[],[f116])).
% 0.20/0.60  fof(f78,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f41])).
% 0.20/0.60  fof(f41,plain,(
% 0.20/0.60    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.60    inference(flattening,[],[f40])).
% 0.20/0.60  fof(f40,plain,(
% 0.20/0.60    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.60    inference(ennf_transformation,[],[f19])).
% 0.20/0.60  fof(f19,axiom,(
% 0.20/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.60  fof(f131,plain,(
% 0.20/0.60    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_9),
% 0.20/0.60    inference(avatar_component_clause,[],[f129])).
% 0.20/0.60  fof(f830,plain,(
% 0.20/0.60    ~spl5_65 | spl5_51 | ~spl5_53),
% 0.20/0.60    inference(avatar_split_clause,[],[f815,f713,f697,f827])).
% 0.20/0.60  fof(f697,plain,(
% 0.20/0.60    spl5_51 <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 0.20/0.60  fof(f713,plain,(
% 0.20/0.60    spl5_53 <=> k1_xboole_0 = sK2),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 0.20/0.60  fof(f815,plain,(
% 0.20/0.60    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0) | (spl5_51 | ~spl5_53)),
% 0.20/0.60    inference(backward_demodulation,[],[f699,f715])).
% 0.20/0.60  fof(f715,plain,(
% 0.20/0.60    k1_xboole_0 = sK2 | ~spl5_53),
% 0.20/0.60    inference(avatar_component_clause,[],[f713])).
% 0.20/0.60  fof(f699,plain,(
% 0.20/0.60    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl5_51),
% 0.20/0.60    inference(avatar_component_clause,[],[f697])).
% 0.20/0.60  fof(f825,plain,(
% 0.20/0.60    spl5_42 | ~spl5_38 | ~spl5_53),
% 0.20/0.60    inference(avatar_split_clause,[],[f824,f713,f586,f606])).
% 0.20/0.60  fof(f586,plain,(
% 0.20/0.60    spl5_38 <=> r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.20/0.60  fof(f824,plain,(
% 0.20/0.60    r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0) | (~spl5_38 | ~spl5_53)),
% 0.20/0.60    inference(forward_demodulation,[],[f814,f83])).
% 0.20/0.60  fof(f814,plain,(
% 0.20/0.60    r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k1_xboole_0)) | (~spl5_38 | ~spl5_53)),
% 0.20/0.60    inference(backward_demodulation,[],[f587,f715])).
% 0.20/0.60  fof(f587,plain,(
% 0.20/0.60    r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2)) | ~spl5_38),
% 0.20/0.60    inference(avatar_component_clause,[],[f586])).
% 0.20/0.60  fof(f811,plain,(
% 0.20/0.60    spl5_52 | ~spl5_54 | ~spl5_60),
% 0.20/0.60    inference(avatar_split_clause,[],[f808,f772,f718,f709])).
% 0.20/0.60  fof(f709,plain,(
% 0.20/0.60    spl5_52 <=> sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 0.20/0.60  fof(f718,plain,(
% 0.20/0.60    spl5_54 <=> k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 0.20/0.60  fof(f808,plain,(
% 0.20/0.60    sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | (~spl5_54 | ~spl5_60)),
% 0.20/0.60    inference(backward_demodulation,[],[f720,f773])).
% 0.20/0.60  fof(f720,plain,(
% 0.20/0.60    k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~spl5_54),
% 0.20/0.60    inference(avatar_component_clause,[],[f718])).
% 0.20/0.60  fof(f807,plain,(
% 0.20/0.60    spl5_60 | ~spl5_3 | ~spl5_44 | ~spl5_56),
% 0.20/0.60    inference(avatar_split_clause,[],[f800,f745,f618,f101,f772])).
% 0.20/0.60  fof(f101,plain,(
% 0.20/0.60    spl5_3 <=> r1_tarski(sK1,sK0)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.60  fof(f618,plain,(
% 0.20/0.60    spl5_44 <=> v1_relat_1(sK4)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 0.20/0.60  fof(f745,plain,(
% 0.20/0.60    spl5_56 <=> sK0 = k1_relat_1(sK4)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 0.20/0.60  fof(f800,plain,(
% 0.20/0.60    sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_3 | ~spl5_44 | ~spl5_56)),
% 0.20/0.60    inference(resolution,[],[f750,f103])).
% 0.20/0.60  fof(f103,plain,(
% 0.20/0.60    r1_tarski(sK1,sK0) | ~spl5_3),
% 0.20/0.60    inference(avatar_component_clause,[],[f101])).
% 0.20/0.60  fof(f750,plain,(
% 0.20/0.60    ( ! [X1] : (~r1_tarski(X1,sK0) | k1_relat_1(k7_relat_1(sK4,X1)) = X1) ) | (~spl5_44 | ~spl5_56)),
% 0.20/0.60    inference(backward_demodulation,[],[f641,f747])).
% 0.20/0.60  fof(f747,plain,(
% 0.20/0.60    sK0 = k1_relat_1(sK4) | ~spl5_56),
% 0.20/0.60    inference(avatar_component_clause,[],[f745])).
% 0.20/0.60  fof(f641,plain,(
% 0.20/0.60    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK4)) | k1_relat_1(k7_relat_1(sK4,X1)) = X1) ) | ~spl5_44),
% 0.20/0.60    inference(resolution,[],[f619,f58])).
% 0.20/0.60  fof(f58,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 0.20/0.60    inference(cnf_transformation,[],[f30])).
% 0.20/0.60  fof(f30,plain,(
% 0.20/0.60    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.60    inference(flattening,[],[f29])).
% 0.20/0.60  fof(f29,plain,(
% 0.20/0.60    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.60    inference(ennf_transformation,[],[f12])).
% 0.20/0.60  fof(f12,axiom,(
% 0.20/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.20/0.60  fof(f619,plain,(
% 0.20/0.60    v1_relat_1(sK4) | ~spl5_44),
% 0.20/0.60    inference(avatar_component_clause,[],[f618])).
% 0.20/0.60  fof(f768,plain,(
% 0.20/0.60    ~spl5_6 | ~spl5_4 | spl5_59 | ~spl5_4 | ~spl5_6),
% 0.20/0.60    inference(avatar_split_clause,[],[f760,f116,f106,f766,f106,f116])).
% 0.20/0.60  fof(f760,plain,(
% 0.20/0.60    ( ! [X1] : (v1_funct_1(k7_relat_1(sK4,X1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4)) ) | (~spl5_4 | ~spl5_6)),
% 0.20/0.60    inference(superposition,[],[f79,f558])).
% 0.20/0.60  fof(f79,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f43])).
% 0.20/0.60  fof(f43,plain,(
% 0.20/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.60    inference(flattening,[],[f42])).
% 0.20/0.60  fof(f42,plain,(
% 0.20/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.60    inference(ennf_transformation,[],[f18])).
% 0.20/0.60  fof(f18,axiom,(
% 0.20/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.20/0.60  fof(f749,plain,(
% 0.20/0.60    k1_xboole_0 != sK3 | v1_xboole_0(sK3) | ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.60    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.60  fof(f748,plain,(
% 0.20/0.60    ~spl5_5 | spl5_55 | spl5_56 | ~spl5_4 | ~spl5_21),
% 0.20/0.60    inference(avatar_split_clause,[],[f739,f257,f106,f745,f741,f111])).
% 0.20/0.60  fof(f111,plain,(
% 0.20/0.60    spl5_5 <=> v1_funct_2(sK4,sK0,sK3)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.60  fof(f741,plain,(
% 0.20/0.60    spl5_55 <=> k1_xboole_0 = sK3),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 0.20/0.60  fof(f257,plain,(
% 0.20/0.60    spl5_21 <=> k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.60  fof(f739,plain,(
% 0.20/0.60    sK0 = k1_relat_1(sK4) | k1_xboole_0 = sK3 | ~v1_funct_2(sK4,sK0,sK3) | (~spl5_4 | ~spl5_21)),
% 0.20/0.60    inference(forward_demodulation,[],[f736,f259])).
% 0.20/0.60  fof(f259,plain,(
% 0.20/0.60    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) | ~spl5_21),
% 0.20/0.60    inference(avatar_component_clause,[],[f257])).
% 0.20/0.60  fof(f736,plain,(
% 0.20/0.60    k1_xboole_0 = sK3 | sK0 = k1_relset_1(sK0,sK3,sK4) | ~v1_funct_2(sK4,sK0,sK3) | ~spl5_4),
% 0.20/0.60    inference(resolution,[],[f76,f108])).
% 0.20/0.60  fof(f76,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f38])).
% 0.20/0.60  fof(f722,plain,(
% 0.20/0.60    spl5_38 | ~spl5_37),
% 0.20/0.60    inference(avatar_split_clause,[],[f707,f581,f586])).
% 0.20/0.60  fof(f581,plain,(
% 0.20/0.60    spl5_37 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.20/0.60  fof(f707,plain,(
% 0.20/0.60    r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2)) | ~spl5_37),
% 0.20/0.60    inference(resolution,[],[f582,f64])).
% 0.20/0.60  fof(f64,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f5])).
% 0.20/0.60  fof(f582,plain,(
% 0.20/0.60    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_37),
% 0.20/0.60    inference(avatar_component_clause,[],[f581])).
% 1.81/0.60  % (8938)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.81/0.60  fof(f721,plain,(
% 1.81/0.60    spl5_54 | ~spl5_37),
% 1.81/0.60    inference(avatar_split_clause,[],[f706,f581,f718])).
% 1.81/0.60  fof(f706,plain,(
% 1.81/0.60    k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~spl5_37),
% 1.81/0.60    inference(resolution,[],[f582,f69])).
% 1.81/0.60  fof(f716,plain,(
% 1.81/0.60    spl5_51 | ~spl5_52 | spl5_53 | ~spl5_37),
% 1.81/0.60    inference(avatar_split_clause,[],[f703,f581,f713,f709,f697])).
% 1.81/0.60  fof(f703,plain,(
% 1.81/0.60    k1_xboole_0 = sK2 | sK1 != k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | ~spl5_37),
% 1.81/0.60    inference(resolution,[],[f582,f75])).
% 1.81/0.60  fof(f75,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f38])).
% 1.81/0.60  fof(f700,plain,(
% 1.81/0.60    ~spl5_51 | ~spl5_4 | ~spl5_6 | spl5_8),
% 1.81/0.60    inference(avatar_split_clause,[],[f695,f125,f116,f106,f697])).
% 1.81/0.60  fof(f125,plain,(
% 1.81/0.60    spl5_8 <=> v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.81/0.60  fof(f695,plain,(
% 1.81/0.60    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | (~spl5_4 | ~spl5_6 | spl5_8)),
% 1.81/0.60    inference(forward_demodulation,[],[f127,f558])).
% 1.81/0.60  fof(f127,plain,(
% 1.81/0.60    ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | spl5_8),
% 1.81/0.60    inference(avatar_component_clause,[],[f125])).
% 1.81/0.60  fof(f693,plain,(
% 1.81/0.60    ~spl5_39 | ~spl5_49 | ~spl5_28 | spl5_37 | ~spl5_44),
% 1.81/0.60    inference(avatar_split_clause,[],[f692,f618,f581,f421,f659,f591])).
% 1.81/0.60  fof(f591,plain,(
% 1.81/0.60    spl5_39 <=> v1_relat_1(k7_relat_1(sK4,sK1))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 1.81/0.60  fof(f659,plain,(
% 1.81/0.60    spl5_49 <=> r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 1.81/0.60  fof(f421,plain,(
% 1.81/0.60    spl5_28 <=> r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.81/0.60  fof(f692,plain,(
% 1.81/0.60    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | (spl5_37 | ~spl5_44)),
% 1.81/0.60    inference(forward_demodulation,[],[f668,f640])).
% 1.81/0.60  fof(f640,plain,(
% 1.81/0.60    ( ! [X0] : (k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0))) ) | ~spl5_44),
% 1.81/0.60    inference(resolution,[],[f619,f57])).
% 1.81/0.60  fof(f57,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f28])).
% 1.81/0.60  fof(f28,plain,(
% 1.81/0.60    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.81/0.60    inference(ennf_transformation,[],[f9])).
% 1.81/0.60  fof(f9,axiom,(
% 1.81/0.60    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.81/0.60  fof(f668,plain,(
% 1.81/0.60    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK4,sK1)) | spl5_37),
% 1.81/0.60    inference(resolution,[],[f583,f68])).
% 1.81/0.60  fof(f68,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f34])).
% 1.81/0.60  fof(f34,plain,(
% 1.81/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.81/0.60    inference(flattening,[],[f33])).
% 1.81/0.60  fof(f33,plain,(
% 1.81/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.81/0.60    inference(ennf_transformation,[],[f16])).
% 1.81/0.60  fof(f16,axiom,(
% 1.81/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 1.81/0.60  fof(f583,plain,(
% 1.81/0.60    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_37),
% 1.81/0.60    inference(avatar_component_clause,[],[f581])).
% 1.81/0.60  fof(f691,plain,(
% 1.81/0.60    ~spl5_44 | spl5_49),
% 1.81/0.60    inference(avatar_split_clause,[],[f689,f659,f618])).
% 1.81/0.60  fof(f689,plain,(
% 1.81/0.60    ~v1_relat_1(sK4) | spl5_49),
% 1.81/0.60    inference(resolution,[],[f661,f56])).
% 1.81/0.60  fof(f56,plain,(
% 1.81/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f27])).
% 1.81/0.60  fof(f27,plain,(
% 1.81/0.60    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.81/0.60    inference(ennf_transformation,[],[f11])).
% 1.81/0.60  fof(f11,axiom,(
% 1.81/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.81/0.60  fof(f661,plain,(
% 1.81/0.60    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | spl5_49),
% 1.81/0.60    inference(avatar_component_clause,[],[f659])).
% 1.81/0.60  fof(f662,plain,(
% 1.81/0.60    ~spl5_49 | ~spl5_28 | ~spl5_39 | ~spl5_4 | ~spl5_6 | spl5_7 | ~spl5_44),
% 1.81/0.60    inference(avatar_split_clause,[],[f657,f618,f121,f116,f106,f591,f421,f659])).
% 1.81/0.60  fof(f121,plain,(
% 1.81/0.60    spl5_7 <=> m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.81/0.60  fof(f657,plain,(
% 1.81/0.60    ~v1_relat_1(k7_relat_1(sK4,sK1)) | ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | (~spl5_4 | ~spl5_6 | spl5_7 | ~spl5_44)),
% 1.81/0.60    inference(forward_demodulation,[],[f656,f558])).
% 1.81/0.60  fof(f656,plain,(
% 1.81/0.60    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | (~spl5_4 | ~spl5_6 | spl5_7 | ~spl5_44)),
% 1.81/0.60    inference(forward_demodulation,[],[f655,f640])).
% 1.81/0.60  fof(f655,plain,(
% 1.81/0.60    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | (~spl5_4 | ~spl5_6 | spl5_7)),
% 1.81/0.60    inference(forward_demodulation,[],[f654,f558])).
% 1.81/0.60  fof(f654,plain,(
% 1.81/0.60    ~r1_tarski(k1_relat_1(k7_relat_1(sK4,sK1)),sK1) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | (~spl5_4 | ~spl5_6 | spl5_7)),
% 1.81/0.60    inference(forward_demodulation,[],[f542,f558])).
% 1.81/0.60  fof(f542,plain,(
% 1.81/0.60    ~r1_tarski(k1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK1) | ~r1_tarski(k2_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)),sK2) | ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_7),
% 1.81/0.60    inference(resolution,[],[f123,f68])).
% 1.81/0.60  fof(f123,plain,(
% 1.81/0.60    ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_7),
% 1.81/0.60    inference(avatar_component_clause,[],[f121])).
% 1.81/0.60  fof(f639,plain,(
% 1.81/0.60    ~spl5_4 | spl5_44),
% 1.81/0.60    inference(avatar_contradiction_clause,[],[f637])).
% 1.81/0.60  fof(f637,plain,(
% 1.81/0.60    $false | (~spl5_4 | spl5_44)),
% 1.81/0.60    inference(unit_resulting_resolution,[],[f54,f108,f620,f53])).
% 1.81/0.60  fof(f53,plain,(
% 1.81/0.60    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f25])).
% 1.81/0.60  fof(f25,plain,(
% 1.81/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.81/0.60    inference(ennf_transformation,[],[f6])).
% 1.81/0.60  fof(f6,axiom,(
% 1.81/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.81/0.60  fof(f620,plain,(
% 1.81/0.60    ~v1_relat_1(sK4) | spl5_44),
% 1.81/0.60    inference(avatar_component_clause,[],[f618])).
% 1.81/0.60  fof(f54,plain,(
% 1.81/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.81/0.60    inference(cnf_transformation,[],[f8])).
% 1.81/0.60  fof(f8,axiom,(
% 1.81/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.81/0.60  fof(f594,plain,(
% 1.81/0.60    spl5_39 | ~spl5_4 | ~spl5_6 | ~spl5_29),
% 1.81/0.60    inference(avatar_split_clause,[],[f565,f446,f116,f106,f591])).
% 1.81/0.60  fof(f446,plain,(
% 1.81/0.60    spl5_29 <=> v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 1.81/0.60  fof(f565,plain,(
% 1.81/0.60    v1_relat_1(k7_relat_1(sK4,sK1)) | (~spl5_4 | ~spl5_6 | ~spl5_29)),
% 1.81/0.60    inference(backward_demodulation,[],[f447,f558])).
% 1.81/0.60  fof(f447,plain,(
% 1.81/0.60    v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~spl5_29),
% 1.81/0.60    inference(avatar_component_clause,[],[f446])).
% 1.81/0.60  fof(f514,plain,(
% 1.81/0.60    ~spl5_6 | ~spl5_4 | spl5_29),
% 1.81/0.60    inference(avatar_split_clause,[],[f505,f446,f106,f116])).
% 1.81/0.60  fof(f505,plain,(
% 1.81/0.60    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | ~v1_funct_1(sK4) | spl5_29),
% 1.81/0.60    inference(resolution,[],[f80,f461])).
% 1.81/0.60  fof(f461,plain,(
% 1.81/0.60    ( ! [X2,X3] : (~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | spl5_29),
% 1.81/0.60    inference(resolution,[],[f458,f54])).
% 1.81/0.60  fof(f458,plain,(
% 1.81/0.60    ( ! [X0] : (~v1_relat_1(X0) | ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(X0))) ) | spl5_29),
% 1.81/0.60    inference(resolution,[],[f448,f53])).
% 1.81/0.60  fof(f448,plain,(
% 1.81/0.60    ~v1_relat_1(k2_partfun1(sK0,sK3,sK4,sK1)) | spl5_29),
% 1.81/0.60    inference(avatar_component_clause,[],[f446])).
% 1.81/0.60  fof(f80,plain,(
% 1.81/0.60    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f43])).
% 1.81/0.60  fof(f424,plain,(
% 1.81/0.60    spl5_28 | ~spl5_2 | ~spl5_4),
% 1.81/0.60    inference(avatar_split_clause,[],[f419,f106,f96,f421])).
% 1.81/0.60  fof(f96,plain,(
% 1.81/0.60    spl5_2 <=> r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.81/0.60  fof(f419,plain,(
% 1.81/0.60    r1_tarski(k9_relat_1(sK4,sK1),sK2) | (~spl5_2 | ~spl5_4)),
% 1.81/0.60    inference(backward_demodulation,[],[f98,f415])).
% 1.81/0.60  fof(f415,plain,(
% 1.81/0.60    ( ! [X0] : (k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0)) ) | ~spl5_4),
% 1.81/0.60    inference(resolution,[],[f77,f108])).
% 1.81/0.60  fof(f77,plain,(
% 1.81/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.81/0.60    inference(cnf_transformation,[],[f39])).
% 1.81/0.60  fof(f39,plain,(
% 1.81/0.60    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.60    inference(ennf_transformation,[],[f15])).
% 1.81/0.60  fof(f15,axiom,(
% 1.81/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.81/0.60  fof(f98,plain,(
% 1.81/0.60    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) | ~spl5_2),
% 1.81/0.60    inference(avatar_component_clause,[],[f96])).
% 1.81/0.60  fof(f313,plain,(
% 1.81/0.60    spl5_23 | ~spl5_19 | ~spl5_25),
% 1.81/0.60    inference(avatar_split_clause,[],[f312,f308,f210,f292])).
% 1.81/0.60  fof(f210,plain,(
% 1.81/0.60    spl5_19 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0))),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.81/0.60  fof(f308,plain,(
% 1.81/0.60    spl5_25 <=> k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.81/0.60  fof(f312,plain,(
% 1.81/0.60    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl5_19 | ~spl5_25)),
% 1.81/0.60    inference(backward_demodulation,[],[f212,f310])).
% 1.81/0.60  fof(f310,plain,(
% 1.81/0.60    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | ~spl5_25),
% 1.81/0.60    inference(avatar_component_clause,[],[f308])).
% 1.81/0.60  fof(f212,plain,(
% 1.81/0.60    k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) | ~spl5_19),
% 1.81/0.60    inference(avatar_component_clause,[],[f210])).
% 1.81/0.60  fof(f311,plain,(
% 1.81/0.60    spl5_25 | ~spl5_12 | ~spl5_13),
% 1.81/0.60    inference(avatar_split_clause,[],[f302,f152,f146,f308])).
% 1.81/0.60  fof(f152,plain,(
% 1.81/0.60    spl5_13 <=> v1_relat_1(k1_xboole_0)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.81/0.60  fof(f302,plain,(
% 1.81/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) | ~spl5_13),
% 1.81/0.60    inference(superposition,[],[f226,f84])).
% 1.81/0.60  fof(f226,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl5_13),
% 1.81/0.60    inference(resolution,[],[f223,f70])).
% 1.81/0.60  fof(f70,plain,(
% 1.81/0.60    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/0.60    inference(cnf_transformation,[],[f36])).
% 1.81/0.60  fof(f36,plain,(
% 1.81/0.60    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.60    inference(ennf_transformation,[],[f22])).
% 1.81/0.60  fof(f22,plain,(
% 1.81/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.81/0.60    inference(pure_predicate_removal,[],[f13])).
% 1.81/0.60  fof(f13,axiom,(
% 1.81/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.81/0.60  fof(f223,plain,(
% 1.81/0.60    ( ! [X3] : (~v4_relat_1(k1_xboole_0,X3) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X3)) ) | ~spl5_13),
% 1.81/0.60    inference(resolution,[],[f59,f154])).
% 1.81/0.60  fof(f154,plain,(
% 1.81/0.60    v1_relat_1(k1_xboole_0) | ~spl5_13),
% 1.81/0.60    inference(avatar_component_clause,[],[f152])).
% 1.81/0.60  fof(f59,plain,(
% 1.81/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 1.81/0.60    inference(cnf_transformation,[],[f32])).
% 1.81/0.60  fof(f32,plain,(
% 1.81/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.81/0.60    inference(flattening,[],[f31])).
% 1.81/0.60  fof(f31,plain,(
% 1.81/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.81/0.60    inference(ennf_transformation,[],[f10])).
% 1.81/0.60  fof(f10,axiom,(
% 1.81/0.60    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.81/0.60  fof(f260,plain,(
% 1.81/0.60    spl5_21 | ~spl5_4),
% 1.81/0.60    inference(avatar_split_clause,[],[f252,f106,f257])).
% 1.81/0.60  fof(f252,plain,(
% 1.81/0.60    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) | ~spl5_4),
% 1.81/0.60    inference(resolution,[],[f69,f108])).
% 1.81/0.60  fof(f213,plain,(
% 1.81/0.60    spl5_19 | ~spl5_13),
% 1.81/0.60    inference(avatar_split_clause,[],[f206,f152,f210])).
% 1.81/0.60  fof(f206,plain,(
% 1.81/0.60    k1_xboole_0 = k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) | ~spl5_13),
% 1.81/0.60    inference(resolution,[],[f204,f154])).
% 1.81/0.60  fof(f204,plain,(
% 1.81/0.60    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k1_relat_1(k7_relat_1(X0,k1_xboole_0))) )),
% 1.81/0.60    inference(resolution,[],[f180,f56])).
% 1.81/0.60  fof(f160,plain,(
% 1.81/0.60    spl5_12),
% 1.81/0.60    inference(avatar_contradiction_clause,[],[f157])).
% 1.81/0.60  fof(f157,plain,(
% 1.81/0.60    $false | spl5_12),
% 1.81/0.60    inference(unit_resulting_resolution,[],[f52,f148,f63])).
% 1.81/0.60  fof(f148,plain,(
% 1.81/0.60    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl5_12),
% 1.81/0.60    inference(avatar_component_clause,[],[f146])).
% 1.81/0.60  fof(f155,plain,(
% 1.81/0.60    spl5_13),
% 1.81/0.60    inference(avatar_split_clause,[],[f150,f152])).
% 1.81/0.60  fof(f150,plain,(
% 1.81/0.60    v1_relat_1(k1_xboole_0)),
% 1.81/0.60    inference(superposition,[],[f54,f83])).
% 1.81/0.60  fof(f137,plain,(
% 1.81/0.60    spl5_10),
% 1.81/0.60    inference(avatar_split_clause,[],[f51,f134])).
% 1.81/0.60  fof(f134,plain,(
% 1.81/0.60    spl5_10 <=> v1_xboole_0(k1_xboole_0)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.81/0.60  fof(f51,plain,(
% 1.81/0.60    v1_xboole_0(k1_xboole_0)),
% 1.81/0.60    inference(cnf_transformation,[],[f1])).
% 1.81/0.60  fof(f1,axiom,(
% 1.81/0.60    v1_xboole_0(k1_xboole_0)),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.81/0.60  fof(f132,plain,(
% 1.81/0.60    ~spl5_7 | ~spl5_8 | ~spl5_9),
% 1.81/0.60    inference(avatar_split_clause,[],[f44,f129,f125,f121])).
% 1.81/0.60  fof(f44,plain,(
% 1.81/0.60    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.81/0.60    inference(cnf_transformation,[],[f24])).
% 1.81/0.60  fof(f24,plain,(
% 1.81/0.60    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 1.81/0.60    inference(flattening,[],[f23])).
% 1.81/0.60  fof(f23,plain,(
% 1.81/0.60    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 1.81/0.60    inference(ennf_transformation,[],[f21])).
% 1.81/0.60  fof(f21,negated_conjecture,(
% 1.81/0.60    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.81/0.60    inference(negated_conjecture,[],[f20])).
% 1.81/0.60  fof(f20,conjecture,(
% 1.81/0.60    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.81/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).
% 1.81/0.60  fof(f119,plain,(
% 1.81/0.60    spl5_6),
% 1.81/0.60    inference(avatar_split_clause,[],[f45,f116])).
% 1.81/0.60  fof(f45,plain,(
% 1.81/0.60    v1_funct_1(sK4)),
% 1.81/0.60    inference(cnf_transformation,[],[f24])).
% 1.81/0.60  fof(f114,plain,(
% 1.81/0.60    spl5_5),
% 1.81/0.60    inference(avatar_split_clause,[],[f46,f111])).
% 1.81/0.60  fof(f46,plain,(
% 1.81/0.60    v1_funct_2(sK4,sK0,sK3)),
% 1.81/0.60    inference(cnf_transformation,[],[f24])).
% 1.81/0.60  fof(f109,plain,(
% 1.81/0.60    spl5_4),
% 1.81/0.60    inference(avatar_split_clause,[],[f47,f106])).
% 1.81/0.60  fof(f47,plain,(
% 1.81/0.60    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.81/0.60    inference(cnf_transformation,[],[f24])).
% 1.81/0.60  fof(f104,plain,(
% 1.81/0.60    spl5_3),
% 1.81/0.60    inference(avatar_split_clause,[],[f48,f101])).
% 1.81/0.60  fof(f48,plain,(
% 1.81/0.60    r1_tarski(sK1,sK0)),
% 1.81/0.60    inference(cnf_transformation,[],[f24])).
% 1.81/0.60  fof(f99,plain,(
% 1.81/0.60    spl5_2),
% 1.81/0.60    inference(avatar_split_clause,[],[f49,f96])).
% 1.81/0.60  fof(f49,plain,(
% 1.81/0.60    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 1.81/0.60    inference(cnf_transformation,[],[f24])).
% 1.81/0.60  fof(f94,plain,(
% 1.81/0.60    ~spl5_1),
% 1.81/0.60    inference(avatar_split_clause,[],[f50,f91])).
% 1.81/0.60  fof(f91,plain,(
% 1.81/0.60    spl5_1 <=> v1_xboole_0(sK3)),
% 1.81/0.60    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.81/0.60  fof(f50,plain,(
% 1.81/0.60    ~v1_xboole_0(sK3)),
% 1.81/0.60    inference(cnf_transformation,[],[f24])).
% 1.81/0.60  % SZS output end Proof for theBenchmark
% 1.81/0.60  % (8937)------------------------------
% 1.81/0.60  % (8937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.60  % (8937)Termination reason: Refutation
% 1.81/0.60  
% 1.81/0.60  % (8937)Memory used [KB]: 6908
% 1.81/0.60  % (8937)Time elapsed: 0.170 s
% 1.81/0.60  % (8937)------------------------------
% 1.81/0.60  % (8937)------------------------------
% 1.81/0.60  % (8921)Success in time 0.254 s
%------------------------------------------------------------------------------
