%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t30_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:43 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 327 expanded)
%              Number of leaves         :   29 ( 118 expanded)
%              Depth                    :   14
%              Number of atoms          :  613 (1442 expanded)
%              Number of equality atoms :  107 ( 298 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3972,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f105,f112,f116,f127,f131,f135,f139,f161,f183,f187,f221,f233,f271,f289,f366,f2972,f2975,f2989,f3867,f3872,f3900,f3971])).

fof(f3971,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_5
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_460 ),
    inference(avatar_contradiction_clause,[],[f3970])).

fof(f3970,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f3969,f232])).

fof(f232,plain,
    ( k1_relat_1(sK4) = sK1
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl6_38
  <=> k1_relat_1(sK4) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f3969,plain,
    ( k1_relat_1(sK4) != sK1
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_32
    | ~ spl6_460 ),
    inference(forward_demodulation,[],[f3968,f220])).

fof(f220,plain,
    ( k2_relat_1(sK3) = sK1
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl6_32
  <=> k2_relat_1(sK3) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f3968,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f3967,f108])).

fof(f108,plain,
    ( ~ v2_funct_1(sK4)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl6_5
  <=> ~ v2_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f3967,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f3966,f160])).

fof(f160,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl6_22
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f3966,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_24
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f3965,f104])).

fof(f104,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f3965,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4)
    | ~ spl6_0
    | ~ spl6_24
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f3964,f182])).

fof(f182,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl6_24
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f3964,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4)
    | ~ spl6_0
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f3957,f100])).

fof(f100,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_0
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f3957,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4)
    | ~ spl6_460 ),
    inference(resolution,[],[f2725,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t30_funct_2.p',t48_funct_1)).

fof(f2725,plain,
    ( v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ spl6_460 ),
    inference(avatar_component_clause,[],[f2724])).

fof(f2724,plain,
    ( spl6_460
  <=> v2_funct_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_460])])).

fof(f3900,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_7
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_460 ),
    inference(avatar_contradiction_clause,[],[f3899])).

fof(f3899,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_32
    | ~ spl6_38
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f2734,f232])).

fof(f2734,plain,
    ( k1_relat_1(sK4) != sK1
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_32
    | ~ spl6_460 ),
    inference(forward_demodulation,[],[f2733,f220])).

fof(f2733,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f2732,f111])).

fof(f111,plain,
    ( ~ v2_funct_1(sK3)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_7
  <=> ~ v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f2732,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f2731,f160])).

fof(f2731,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_24
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f2730,f104])).

fof(f2730,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_24
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f2729,f182])).

fof(f2729,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f2727,f100])).

fof(f2727,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK3)
    | ~ spl6_460 ),
    inference(resolution,[],[f2725,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3872,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) != k5_relat_1(sK3,sK4)
    | v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(theory_axiom,[])).

fof(f3867,plain,
    ( spl6_606
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f583,f137,f129,f103,f99,f3865])).

fof(f3865,plain,
    ( spl6_606
  <=> k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_606])])).

fof(f129,plain,
    ( spl6_16
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f137,plain,
    ( spl6_20
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f583,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f574,f100])).

fof(f574,plain,
    ( ~ v1_funct_1(sK4)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_20 ),
    inference(resolution,[],[f179,f130])).

fof(f130,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f129])).

fof(f179,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X6)
        | k1_partfun1(sK0,sK1,X7,X8,sK3,X6) = k5_relat_1(sK3,X6) )
    | ~ spl6_2
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f169,f104])).

fof(f169,plain,
    ( ! [X6,X8,X7] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | k1_partfun1(sK0,sK1,X7,X8,sK3,X6) = k5_relat_1(sK3,X6) )
    | ~ spl6_20 ),
    inference(resolution,[],[f138,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t30_funct_2.p',redefinition_k1_partfun1)).

fof(f138,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f137])).

fof(f2989,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_5
    | ~ spl6_12
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_32
    | ~ spl6_46
    | ~ spl6_52
    | ~ spl6_460
    | ~ spl6_494 ),
    inference(avatar_contradiction_clause,[],[f2988])).

fof(f2988,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_32
    | ~ spl6_46
    | ~ spl6_52
    | ~ spl6_460
    | ~ spl6_494 ),
    inference(subsumption_resolution,[],[f108,f2982])).

fof(f2982,plain,
    ( v2_funct_1(sK4)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_32
    | ~ spl6_46
    | ~ spl6_52
    | ~ spl6_460
    | ~ spl6_494 ),
    inference(subsumption_resolution,[],[f2981,f2973])).

fof(f2973,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl6_46
    | ~ spl6_52
    | ~ spl6_494 ),
    inference(forward_demodulation,[],[f2971,f2790])).

fof(f2790,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK4)
    | ~ spl6_46
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f314,f270])).

fof(f270,plain,
    ( v1_funct_2(sK4,k1_xboole_0,sK2)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl6_46
  <=> v1_funct_2(sK4,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f314,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK4)
    | ~ v1_funct_2(sK4,k1_xboole_0,sK2)
    | ~ spl6_52 ),
    inference(resolution,[],[f288,f93])).

fof(f93,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t30_funct_2.p',d1_funct_2)).

fof(f288,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl6_52
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f2971,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_494 ),
    inference(avatar_component_clause,[],[f2970])).

fof(f2970,plain,
    ( spl6_494
  <=> k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_494])])).

fof(f2981,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | v2_funct_1(sK4)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_32
    | ~ spl6_460 ),
    inference(forward_demodulation,[],[f2980,f123])).

fof(f123,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl6_12
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f2980,plain,
    ( k1_relat_1(sK4) != sK1
    | v2_funct_1(sK4)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_32
    | ~ spl6_460 ),
    inference(forward_demodulation,[],[f2979,f220])).

fof(f2979,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f2978,f160])).

fof(f2978,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_24
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f2977,f104])).

fof(f2977,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4)
    | ~ spl6_0
    | ~ spl6_24
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f2976,f182])).

fof(f2976,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4)
    | ~ spl6_0
    | ~ spl6_460 ),
    inference(subsumption_resolution,[],[f2728,f100])).

fof(f2728,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4)
    | ~ spl6_460 ),
    inference(resolution,[],[f2725,f78])).

fof(f2975,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | spl6_7
    | ~ spl6_12
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_32
    | ~ spl6_46
    | ~ spl6_52
    | ~ spl6_460
    | ~ spl6_494 ),
    inference(avatar_contradiction_clause,[],[f2974])).

fof(f2974,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_12
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_32
    | ~ spl6_46
    | ~ spl6_52
    | ~ spl6_460
    | ~ spl6_494 ),
    inference(subsumption_resolution,[],[f2973,f2735])).

fof(f2735,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_7
    | ~ spl6_12
    | ~ spl6_22
    | ~ spl6_24
    | ~ spl6_32
    | ~ spl6_460 ),
    inference(forward_demodulation,[],[f2734,f123])).

fof(f2972,plain,
    ( spl6_494
    | ~ spl6_12
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f2788,f364,f122,f2970])).

fof(f364,plain,
    ( spl6_68
  <=> k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f2788,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_12
    | ~ spl6_68 ),
    inference(forward_demodulation,[],[f365,f123])).

fof(f365,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f364])).

fof(f366,plain,
    ( spl6_68
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f148,f129,f364])).

fof(f148,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_16 ),
    inference(resolution,[],[f130,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t30_funct_2.p',redefinition_k1_relset_1)).

fof(f289,plain,
    ( spl6_52
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f239,f129,f122,f287])).

fof(f239,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(superposition,[],[f130,f123])).

fof(f271,plain,
    ( spl6_46
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f237,f122,f114,f269])).

fof(f114,plain,
    ( spl6_8
  <=> v1_funct_2(sK4,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f237,plain,
    ( v1_funct_2(sK4,k1_xboole_0,sK2)
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(superposition,[],[f115,f123])).

fof(f115,plain,
    ( v1_funct_2(sK4,sK1,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f233,plain,
    ( spl6_38
    | ~ spl6_8
    | spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f157,f129,f125,f114,f231])).

fof(f125,plain,
    ( spl6_15
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f157,plain,
    ( k1_relat_1(sK4) = sK1
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f148,f152])).

fof(f152,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | ~ spl6_8
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f151,f115])).

fof(f151,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | ~ v1_funct_2(sK4,sK1,sK2)
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f141,f126])).

fof(f126,plain,
    ( k1_xboole_0 != sK2
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f125])).

fof(f141,plain,
    ( k1_xboole_0 = sK2
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | ~ v1_funct_2(sK4,sK1,sK2)
    | ~ spl6_16 ),
    inference(resolution,[],[f130,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f221,plain,
    ( spl6_32
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f176,f137,f133,f219])).

fof(f133,plain,
    ( spl6_18
  <=> k2_relset_1(sK0,sK1,sK3) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f176,plain,
    ( k2_relat_1(sK3) = sK1
    | ~ spl6_18
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f166,f134])).

fof(f134,plain,
    ( k2_relset_1(sK0,sK1,sK3) = sK1
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f133])).

fof(f166,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl6_20 ),
    inference(resolution,[],[f138,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t30_funct_2.p',redefinition_k2_relset_1)).

fof(f187,plain,(
    spl6_26 ),
    inference(avatar_split_clause,[],[f62,f185])).

fof(f185,plain,
    ( spl6_26
  <=> v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f62,plain,(
    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(X3) )
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & k2_relset_1(X0,X1,X3) = X1
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(X3) )
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & k2_relset_1(X0,X1,X3) = X1
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( k2_relset_1(X0,X1,X3) = X1
                & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
             => ( ( v2_funct_1(X4)
                  & v2_funct_1(X3) )
                | ( k1_xboole_0 != X1
                  & k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t30_funct_2.p',t30_funct_2)).

fof(f183,plain,
    ( spl6_24
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f172,f137,f181])).

fof(f172,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_20 ),
    inference(resolution,[],[f138,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t30_funct_2.p',cc1_relset_1)).

fof(f161,plain,
    ( spl6_22
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f149,f129,f159])).

fof(f149,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_16 ),
    inference(resolution,[],[f130,f90])).

fof(f139,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f66,f137])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f135,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f63,f133])).

fof(f63,plain,(
    k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f131,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f61,f129])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f127,plain,
    ( spl6_12
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f58,f125,f122])).

fof(f58,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f116,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f60,f114])).

fof(f60,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f112,plain,
    ( ~ spl6_5
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f57,f110,f107])).

fof(f57,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f105,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f64,f103])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f101,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f59,f99])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
