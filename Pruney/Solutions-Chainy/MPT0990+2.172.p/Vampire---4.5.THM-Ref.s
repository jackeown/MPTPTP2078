%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 333 expanded)
%              Number of leaves         :   40 ( 119 expanded)
%              Depth                    :   11
%              Number of atoms          :  584 (1672 expanded)
%              Number of equality atoms :  130 ( 490 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f492,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f101,f105,f112,f163,f168,f182,f196,f198,f203,f214,f223,f228,f239,f264,f266,f314,f377,f400,f425,f441,f443,f454,f460,f463,f475,f489])).

fof(f489,plain,(
    ~ spl4_31 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f44,f394])).

fof(f394,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl4_31
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f44,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

% (8579)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f475,plain,
    ( spl4_31
    | ~ spl4_3
    | ~ spl4_19
    | ~ spl4_37
    | ~ spl4_1
    | ~ spl4_18
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_40
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f474,f457,f450,f192,f178,f255,f85,f429,f259,f94,f392])).

fof(f94,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f259,plain,
    ( spl4_19
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f429,plain,
    ( spl4_37
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f85,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f255,plain,
    ( spl4_18
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f178,plain,
    ( spl4_14
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f192,plain,
    ( spl4_16
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f450,plain,
    ( spl4_40
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f457,plain,
    ( spl4_41
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f474,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_40
    | ~ spl4_41 ),
    inference(trivial_inequality_removal,[],[f473])).

fof(f473,plain,
    ( sK1 != sK1
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_40
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f472,f180])).

fof(f180,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f178])).

fof(f472,plain,
    ( sK1 != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_16
    | ~ spl4_40
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f471,f452])).

fof(f452,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f450])).

fof(f471,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_16
    | ~ spl4_41 ),
    inference(trivial_inequality_removal,[],[f470])).

fof(f470,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_16
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f468,f194])).

fof(f194,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f192])).

fof(f468,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_41 ),
    inference(superposition,[],[f54,f459])).

fof(f459,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f457])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f463,plain,(
    spl4_38 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | spl4_38 ),
    inference(unit_resulting_resolution,[],[f47,f38,f435,f295])).

fof(f295,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f70,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f435,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_38 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl4_38
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f38,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f460,plain,
    ( ~ spl4_38
    | spl4_41
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f455,f438,f457,f433])).

fof(f438,plain,
    ( spl4_39
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f455,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_39 ),
    inference(resolution,[],[f440,f166])).

fof(f166,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X3,X3,X2,k6_relat_1(X3))
      | k6_relat_1(X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f67,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f50,f48])).

fof(f48,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f440,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f438])).

fof(f454,plain,
    ( ~ spl4_3
    | ~ spl4_19
    | ~ spl4_18
    | spl4_40
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f445,f421,f450,f255,f259,f94])).

fof(f421,plain,
    ( spl4_36
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f445,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_36 ),
    inference(superposition,[],[f52,f423])).

fof(f423,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f421])).

fof(f52,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f443,plain,(
    spl4_37 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | spl4_37 ),
    inference(subsumption_resolution,[],[f36,f431])).

fof(f431,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_37 ),
    inference(avatar_component_clause,[],[f429])).

fof(f36,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f441,plain,
    ( ~ spl4_18
    | ~ spl4_13
    | ~ spl4_37
    | ~ spl4_15
    | spl4_39 ),
    inference(avatar_split_clause,[],[f427,f438,f188,f429,f174,f255])).

fof(f174,plain,
    ( spl4_13
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f188,plain,
    ( spl4_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f427,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f71,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f71,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f40,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f425,plain,
    ( ~ spl4_29
    | spl4_36
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f418,f397,f421,f374])).

fof(f374,plain,
    ( spl4_29
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f397,plain,
    ( spl4_32
  <=> sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f418,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_32 ),
    inference(superposition,[],[f56,f399])).

fof(f399,plain,
    ( sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f397])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f400,plain,
    ( ~ spl4_22
    | spl4_32
    | spl4_9
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f379,f374,f145,f397,f311])).

fof(f311,plain,
    ( spl4_22
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f145,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f379,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_29 ),
    inference(resolution,[],[f376,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f376,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f374])).

fof(f377,plain,
    ( spl4_29
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f372,f150,f188,f259,f255,f374])).

fof(f150,plain,
    ( spl4_10
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f372,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(trivial_inequality_removal,[],[f371])).

fof(f371,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f65,f39])).

fof(f39,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f314,plain,
    ( spl4_22
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f309,f150,f188,f259,f255,f311])).

fof(f309,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f308])).

fof(f308,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(superposition,[],[f64,f39])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f266,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | spl4_19 ),
    inference(subsumption_resolution,[],[f41,f261])).

fof(f261,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f259])).

fof(f41,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f264,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | spl4_18 ),
    inference(subsumption_resolution,[],[f45,f257])).

fof(f257,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f255])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f239,plain,(
    ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f43,f160])).

fof(f160,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl4_12
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f43,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f228,plain,
    ( ~ spl4_10
    | spl4_11
    | spl4_12 ),
    inference(avatar_split_clause,[],[f225,f158,f154,f150])).

fof(f154,plain,
    ( spl4_11
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f225,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f47,f62])).

fof(f223,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f47,f190])).

fof(f190,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f188])).

fof(f214,plain,(
    ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f42,f147])).

fof(f147,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f145])).

fof(f42,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f17])).

fof(f203,plain,
    ( ~ spl4_7
    | spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f200,f145,f141,f137])).

fof(f137,plain,
    ( spl4_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f141,plain,
    ( spl4_8
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f200,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(resolution,[],[f38,f62])).

fof(f198,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f38,f176])).

fof(f176,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f174])).

fof(f196,plain,
    ( ~ spl4_15
    | spl4_16
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f185,f154,f192,f188])).

fof(f185,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_11 ),
    inference(superposition,[],[f56,f156])).

fof(f156,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f182,plain,
    ( ~ spl4_13
    | spl4_14
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f171,f141,f178,f174])).

% (8582)Refutation not found, incomplete strategy% (8582)------------------------------
% (8582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8582)Termination reason: Refutation not found, incomplete strategy

% (8582)Memory used [KB]: 11001
% (8582)Time elapsed: 0.133 s
% (8582)------------------------------
% (8582)------------------------------
fof(f171,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_8 ),
    inference(superposition,[],[f56,f143])).

fof(f143,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f141])).

fof(f168,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f46,f152])).

fof(f152,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f150])).

fof(f46,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f163,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f37,f139])).

fof(f139,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f37,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f112,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f55,f100])).

fof(f100,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f105,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f55,f91])).

fof(f91,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f101,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f82,f98,f94])).

fof(f82,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f51,f47])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f92,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f81,f89,f85])).

fof(f81,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f51,f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:50:34 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (8558)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (8582)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.52  % (8574)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (8566)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (8564)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (8567)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.52  % (8562)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (8559)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (8573)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (8581)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (8576)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (8555)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (8556)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (8577)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (8555)Refutation not found, incomplete strategy% (8555)------------------------------
% 0.22/0.54  % (8555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8555)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8555)Memory used [KB]: 1791
% 0.22/0.54  % (8555)Time elapsed: 0.127 s
% 0.22/0.54  % (8555)------------------------------
% 0.22/0.54  % (8555)------------------------------
% 0.22/0.54  % (8567)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f492,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f92,f101,f105,f112,f163,f168,f182,f196,f198,f203,f214,f223,f228,f239,f264,f266,f314,f377,f400,f425,f441,f443,f454,f460,f463,f475,f489])).
% 0.22/0.54  fof(f489,plain,(
% 0.22/0.54    ~spl4_31),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f476])).
% 0.22/0.54  fof(f476,plain,(
% 0.22/0.54    $false | ~spl4_31),
% 0.22/0.54    inference(subsumption_resolution,[],[f44,f394])).
% 0.22/0.54  fof(f394,plain,(
% 0.22/0.54    sK3 = k2_funct_1(sK2) | ~spl4_31),
% 0.22/0.54    inference(avatar_component_clause,[],[f392])).
% 0.22/0.54  fof(f392,plain,(
% 0.22/0.54    spl4_31 <=> sK3 = k2_funct_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    sK3 != k2_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  % (8579)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.22/0.54    inference(negated_conjecture,[],[f14])).
% 0.22/0.54  fof(f14,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 0.22/0.54  fof(f475,plain,(
% 0.22/0.54    spl4_31 | ~spl4_3 | ~spl4_19 | ~spl4_37 | ~spl4_1 | ~spl4_18 | ~spl4_14 | ~spl4_16 | ~spl4_40 | ~spl4_41),
% 0.22/0.54    inference(avatar_split_clause,[],[f474,f457,f450,f192,f178,f255,f85,f429,f259,f94,f392])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    spl4_3 <=> v1_relat_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.54  fof(f259,plain,(
% 0.22/0.54    spl4_19 <=> v2_funct_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.54  fof(f429,plain,(
% 0.22/0.54    spl4_37 <=> v1_funct_1(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    spl4_1 <=> v1_relat_1(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.54  fof(f255,plain,(
% 0.22/0.54    spl4_18 <=> v1_funct_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    spl4_14 <=> sK1 = k1_relat_1(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    spl4_16 <=> sK0 = k1_relat_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.54  fof(f450,plain,(
% 0.22/0.54    spl4_40 <=> sK1 = k2_relat_1(sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.22/0.54  fof(f457,plain,(
% 0.22/0.54    spl4_41 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.22/0.54  fof(f474,plain,(
% 0.22/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl4_14 | ~spl4_16 | ~spl4_40 | ~spl4_41)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f473])).
% 0.22/0.54  fof(f473,plain,(
% 0.22/0.54    sK1 != sK1 | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl4_14 | ~spl4_16 | ~spl4_40 | ~spl4_41)),
% 0.22/0.54    inference(forward_demodulation,[],[f472,f180])).
% 0.22/0.54  fof(f180,plain,(
% 0.22/0.54    sK1 = k1_relat_1(sK3) | ~spl4_14),
% 0.22/0.54    inference(avatar_component_clause,[],[f178])).
% 0.22/0.54  fof(f472,plain,(
% 0.22/0.54    sK1 != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl4_16 | ~spl4_40 | ~spl4_41)),
% 0.22/0.54    inference(forward_demodulation,[],[f471,f452])).
% 0.22/0.54  fof(f452,plain,(
% 0.22/0.54    sK1 = k2_relat_1(sK2) | ~spl4_40),
% 0.22/0.54    inference(avatar_component_clause,[],[f450])).
% 0.22/0.54  fof(f471,plain,(
% 0.22/0.54    ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl4_16 | ~spl4_41)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f470])).
% 0.22/0.54  fof(f470,plain,(
% 0.22/0.54    k6_relat_1(sK0) != k6_relat_1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | (~spl4_16 | ~spl4_41)),
% 0.22/0.54    inference(forward_demodulation,[],[f468,f194])).
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    sK0 = k1_relat_1(sK2) | ~spl4_16),
% 0.22/0.54    inference(avatar_component_clause,[],[f192])).
% 0.22/0.54  fof(f468,plain,(
% 0.22/0.54    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k1_relat_1(sK3) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | ~spl4_41),
% 0.22/0.54    inference(superposition,[],[f54,f459])).
% 0.22/0.54  fof(f459,plain,(
% 0.22/0.54    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_41),
% 0.22/0.54    inference(avatar_component_clause,[],[f457])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 0.22/0.54  fof(f463,plain,(
% 0.22/0.54    spl4_38),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f461])).
% 0.22/0.54  fof(f461,plain,(
% 0.22/0.54    $false | spl4_38),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f47,f38,f435,f295])).
% 0.22/0.54  fof(f295,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f294])).
% 0.22/0.54  fof(f294,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(superposition,[],[f70,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.22/0.54  fof(f70,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 0.22/0.54  fof(f435,plain,(
% 0.22/0.54    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_38),
% 0.22/0.54    inference(avatar_component_clause,[],[f433])).
% 0.22/0.54  fof(f433,plain,(
% 0.22/0.54    spl4_38 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f460,plain,(
% 0.22/0.54    ~spl4_38 | spl4_41 | ~spl4_39),
% 0.22/0.54    inference(avatar_split_clause,[],[f455,f438,f457,f433])).
% 0.22/0.54  fof(f438,plain,(
% 0.22/0.54    spl4_39 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.22/0.54  fof(f455,plain,(
% 0.22/0.54    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_39),
% 0.22/0.54    inference(resolution,[],[f440,f166])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r2_relset_1(X3,X3,X2,k6_relat_1(X3)) | k6_relat_1(X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 0.22/0.54    inference(resolution,[],[f67,f72])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f50,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.22/0.54  fof(f440,plain,(
% 0.22/0.54    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_39),
% 0.22/0.54    inference(avatar_component_clause,[],[f438])).
% 0.22/0.54  fof(f454,plain,(
% 0.22/0.54    ~spl4_3 | ~spl4_19 | ~spl4_18 | spl4_40 | ~spl4_36),
% 0.22/0.54    inference(avatar_split_clause,[],[f445,f421,f450,f255,f259,f94])).
% 0.22/0.54  fof(f421,plain,(
% 0.22/0.54    spl4_36 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.54  fof(f445,plain,(
% 0.22/0.54    sK1 = k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_36),
% 0.22/0.54    inference(superposition,[],[f52,f423])).
% 0.22/0.54  fof(f423,plain,(
% 0.22/0.54    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl4_36),
% 0.22/0.54    inference(avatar_component_clause,[],[f421])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(flattening,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.54  fof(f443,plain,(
% 0.22/0.54    spl4_37),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f442])).
% 0.22/0.54  fof(f442,plain,(
% 0.22/0.54    $false | spl4_37),
% 0.22/0.54    inference(subsumption_resolution,[],[f36,f431])).
% 0.22/0.54  fof(f431,plain,(
% 0.22/0.54    ~v1_funct_1(sK3) | spl4_37),
% 0.22/0.54    inference(avatar_component_clause,[],[f429])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    v1_funct_1(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f441,plain,(
% 0.22/0.54    ~spl4_18 | ~spl4_13 | ~spl4_37 | ~spl4_15 | spl4_39),
% 0.22/0.54    inference(avatar_split_clause,[],[f427,f438,f188,f429,f174,f255])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    spl4_13 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.54  fof(f188,plain,(
% 0.22/0.54    spl4_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.54  fof(f427,plain,(
% 0.22/0.54    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2)),
% 0.22/0.54    inference(superposition,[],[f71,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.54    inference(flattening,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 0.22/0.54    inference(definition_unfolding,[],[f40,f48])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f425,plain,(
% 0.22/0.54    ~spl4_29 | spl4_36 | ~spl4_32),
% 0.22/0.54    inference(avatar_split_clause,[],[f418,f397,f421,f374])).
% 0.22/0.54  fof(f374,plain,(
% 0.22/0.54    spl4_29 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.54  fof(f397,plain,(
% 0.22/0.54    spl4_32 <=> sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.22/0.54  fof(f418,plain,(
% 0.22/0.54    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_32),
% 0.22/0.54    inference(superposition,[],[f56,f399])).
% 0.22/0.54  fof(f399,plain,(
% 0.22/0.54    sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~spl4_32),
% 0.22/0.54    inference(avatar_component_clause,[],[f397])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.54  fof(f400,plain,(
% 0.22/0.54    ~spl4_22 | spl4_32 | spl4_9 | ~spl4_29),
% 0.22/0.54    inference(avatar_split_clause,[],[f379,f374,f145,f397,f311])).
% 0.22/0.54  fof(f311,plain,(
% 0.22/0.54    spl4_22 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    spl4_9 <=> k1_xboole_0 = sK0),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.54  fof(f379,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~spl4_29),
% 0.22/0.54    inference(resolution,[],[f376,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.54  fof(f376,plain,(
% 0.22/0.54    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_29),
% 0.22/0.54    inference(avatar_component_clause,[],[f374])).
% 0.22/0.54  fof(f377,plain,(
% 0.22/0.54    spl4_29 | ~spl4_18 | ~spl4_19 | ~spl4_15 | ~spl4_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f372,f150,f188,f259,f255,f374])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    spl4_10 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.54  fof(f372,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f371])).
% 0.22/0.54  fof(f371,plain,(
% 0.22/0.54    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.54    inference(superposition,[],[f65,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.54    inference(flattening,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.54  fof(f314,plain,(
% 0.22/0.54    spl4_22 | ~spl4_18 | ~spl4_19 | ~spl4_15 | ~spl4_10),
% 0.22/0.54    inference(avatar_split_clause,[],[f309,f150,f188,f259,f255,f311])).
% 0.22/0.54  fof(f309,plain,(
% 0.22/0.54    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f308])).
% 0.22/0.54  fof(f308,plain,(
% 0.22/0.54    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.54    inference(superposition,[],[f64,f39])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f266,plain,(
% 0.22/0.54    spl4_19),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f265])).
% 0.22/0.54  fof(f265,plain,(
% 0.22/0.54    $false | spl4_19),
% 0.22/0.54    inference(subsumption_resolution,[],[f41,f261])).
% 0.22/0.54  fof(f261,plain,(
% 0.22/0.54    ~v2_funct_1(sK2) | spl4_19),
% 0.22/0.54    inference(avatar_component_clause,[],[f259])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    v2_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f264,plain,(
% 0.22/0.54    spl4_18),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f263])).
% 0.22/0.54  fof(f263,plain,(
% 0.22/0.54    $false | spl4_18),
% 0.22/0.54    inference(subsumption_resolution,[],[f45,f257])).
% 0.22/0.54  fof(f257,plain,(
% 0.22/0.54    ~v1_funct_1(sK2) | spl4_18),
% 0.22/0.54    inference(avatar_component_clause,[],[f255])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    v1_funct_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f239,plain,(
% 0.22/0.54    ~spl4_12),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f229])).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    $false | ~spl4_12),
% 0.22/0.54    inference(subsumption_resolution,[],[f43,f160])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    k1_xboole_0 = sK1 | ~spl4_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f158])).
% 0.22/0.55  fof(f158,plain,(
% 0.22/0.55    spl4_12 <=> k1_xboole_0 = sK1),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    k1_xboole_0 != sK1),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f228,plain,(
% 0.22/0.55    ~spl4_10 | spl4_11 | spl4_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f225,f158,f154,f150])).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    spl4_11 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.55  fof(f225,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.55    inference(resolution,[],[f47,f62])).
% 0.22/0.55  fof(f223,plain,(
% 0.22/0.55    spl4_15),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f222])).
% 0.22/0.55  fof(f222,plain,(
% 0.22/0.55    $false | spl4_15),
% 0.22/0.55    inference(subsumption_resolution,[],[f47,f190])).
% 0.22/0.55  fof(f190,plain,(
% 0.22/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_15),
% 0.22/0.55    inference(avatar_component_clause,[],[f188])).
% 0.22/0.55  fof(f214,plain,(
% 0.22/0.55    ~spl4_9),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f204])).
% 0.22/0.55  fof(f204,plain,(
% 0.22/0.55    $false | ~spl4_9),
% 0.22/0.55    inference(subsumption_resolution,[],[f42,f147])).
% 0.22/0.55  fof(f147,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | ~spl4_9),
% 0.22/0.55    inference(avatar_component_clause,[],[f145])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    k1_xboole_0 != sK0),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f203,plain,(
% 0.22/0.55    ~spl4_7 | spl4_8 | spl4_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f200,f145,f141,f137])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    spl4_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.55  fof(f141,plain,(
% 0.22/0.55    spl4_8 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.55  fof(f200,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.55    inference(resolution,[],[f38,f62])).
% 0.22/0.55  fof(f198,plain,(
% 0.22/0.55    spl4_13),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f197])).
% 0.22/0.55  fof(f197,plain,(
% 0.22/0.55    $false | spl4_13),
% 0.22/0.55    inference(subsumption_resolution,[],[f38,f176])).
% 0.22/0.55  fof(f176,plain,(
% 0.22/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f174])).
% 0.22/0.55  fof(f196,plain,(
% 0.22/0.55    ~spl4_15 | spl4_16 | ~spl4_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f185,f154,f192,f188])).
% 0.22/0.55  fof(f185,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_11),
% 0.22/0.55    inference(superposition,[],[f56,f156])).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_11),
% 0.22/0.55    inference(avatar_component_clause,[],[f154])).
% 0.22/0.55  fof(f182,plain,(
% 0.22/0.55    ~spl4_13 | spl4_14 | ~spl4_8),
% 0.22/0.55    inference(avatar_split_clause,[],[f171,f141,f178,f174])).
% 0.22/0.55  % (8582)Refutation not found, incomplete strategy% (8582)------------------------------
% 0.22/0.55  % (8582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8582)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8582)Memory used [KB]: 11001
% 0.22/0.55  % (8582)Time elapsed: 0.133 s
% 0.22/0.55  % (8582)------------------------------
% 0.22/0.55  % (8582)------------------------------
% 0.22/0.55  fof(f171,plain,(
% 0.22/0.55    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_8),
% 0.22/0.55    inference(superposition,[],[f56,f143])).
% 0.22/0.55  fof(f143,plain,(
% 0.22/0.55    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f141])).
% 0.22/0.55  fof(f168,plain,(
% 0.22/0.55    spl4_10),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f167])).
% 0.22/0.55  fof(f167,plain,(
% 0.22/0.55    $false | spl4_10),
% 0.22/0.55    inference(subsumption_resolution,[],[f46,f152])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    ~v1_funct_2(sK2,sK0,sK1) | spl4_10),
% 0.22/0.55    inference(avatar_component_clause,[],[f150])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f163,plain,(
% 0.22/0.55    spl4_7),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f162])).
% 0.22/0.55  fof(f162,plain,(
% 0.22/0.55    $false | spl4_7),
% 0.22/0.55    inference(subsumption_resolution,[],[f37,f139])).
% 0.22/0.55  fof(f139,plain,(
% 0.22/0.55    ~v1_funct_2(sK3,sK1,sK0) | spl4_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f137])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    spl4_4),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f109])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    $false | spl4_4),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f55,f100])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f98])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.55  fof(f105,plain,(
% 0.22/0.55    spl4_2),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f102])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    $false | spl4_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f55,f91])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f89])).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.55  fof(f101,plain,(
% 0.22/0.55    spl4_3 | ~spl4_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f82,f98,f94])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 0.22/0.55    inference(resolution,[],[f51,f47])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    spl4_1 | ~spl4_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f81,f89,f85])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 0.22/0.55    inference(resolution,[],[f51,f38])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (8567)------------------------------
% 0.22/0.55  % (8567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8567)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (8567)Memory used [KB]: 6524
% 0.22/0.55  % (8567)Time elapsed: 0.060 s
% 0.22/0.55  % (8567)------------------------------
% 0.22/0.55  % (8567)------------------------------
% 0.22/0.55  % (8554)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (8570)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (8547)Success in time 0.185 s
%------------------------------------------------------------------------------
