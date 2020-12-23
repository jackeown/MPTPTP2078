%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 476 expanded)
%              Number of leaves         :   59 ( 245 expanded)
%              Depth                    :   10
%              Number of atoms          :  870 (2362 expanded)
%              Number of equality atoms :   94 ( 267 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f492,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f88,f92,f96,f100,f104,f108,f112,f116,f120,f124,f140,f152,f188,f195,f202,f208,f226,f231,f242,f246,f264,f267,f280,f306,f311,f357,f417,f422,f437,f451,f462,f467,f475,f481,f484,f490,f491])).

fof(f491,plain,
    ( k1_xboole_0 != sK1
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f490,plain,
    ( ~ spl6_6
    | spl6_68 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | ~ spl6_6
    | spl6_68 ),
    inference(subsumption_resolution,[],[f103,f487])).

fof(f487,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl6_68 ),
    inference(resolution,[],[f474,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f474,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl6_68 ),
    inference(avatar_component_clause,[],[f473])).

fof(f473,plain,
    ( spl6_68
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f103,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f484,plain,(
    spl6_69 ),
    inference(avatar_contradiction_clause,[],[f482])).

fof(f482,plain,
    ( $false
    | spl6_69 ),
    inference(resolution,[],[f480,f62])).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f480,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl6_69 ),
    inference(avatar_component_clause,[],[f479])).

fof(f479,plain,
    ( spl6_69
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f481,plain,
    ( ~ spl6_69
    | ~ spl6_6
    | spl6_67 ),
    inference(avatar_split_clause,[],[f477,f470,f102,f479])).

fof(f470,plain,
    ( spl6_67
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f477,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl6_6
    | spl6_67 ),
    inference(resolution,[],[f476,f103])).

fof(f476,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_67 ),
    inference(resolution,[],[f471,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f471,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_67 ),
    inference(avatar_component_clause,[],[f470])).

fof(f475,plain,
    ( ~ spl6_67
    | ~ spl6_68
    | spl6_66 ),
    inference(avatar_split_clause,[],[f468,f465,f473,f470])).

fof(f465,plain,
    ( spl6_66
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f468,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | spl6_66 ),
    inference(resolution,[],[f466,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f466,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl6_66 ),
    inference(avatar_component_clause,[],[f465])).

fof(f467,plain,
    ( ~ spl6_6
    | ~ spl6_66
    | spl6_65 ),
    inference(avatar_split_clause,[],[f463,f460,f465,f102])).

fof(f460,plain,
    ( spl6_65
  <=> r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f463,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_65 ),
    inference(superposition,[],[f461,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f461,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0)
    | spl6_65 ),
    inference(avatar_component_clause,[],[f460])).

fof(f462,plain,
    ( ~ spl6_4
    | ~ spl6_65
    | ~ spl6_12
    | spl6_62 ),
    inference(avatar_split_clause,[],[f458,f446,f134,f460,f94])).

fof(f94,plain,
    ( spl6_4
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f134,plain,
    ( spl6_12
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f446,plain,
    ( spl6_62
  <=> r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f458,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_12
    | spl6_62 ),
    inference(forward_demodulation,[],[f453,f135])).

fof(f135,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f453,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_62 ),
    inference(superposition,[],[f447,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f447,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | spl6_62 ),
    inference(avatar_component_clause,[],[f446])).

fof(f451,plain,
    ( spl6_10
    | ~ spl6_8
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_62
    | spl6_63
    | spl6_60 ),
    inference(avatar_split_clause,[],[f444,f435,f449,f446,f90,f94,f98,f102,f106,f110,f118])).

fof(f118,plain,
    ( spl6_10
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f110,plain,
    ( spl6_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f106,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f98,plain,
    ( spl6_5
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f90,plain,
    ( spl6_3
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f449,plain,
    ( spl6_63
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f435,plain,
    ( spl6_60
  <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f444,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | spl6_60 ),
    inference(trivial_inequality_removal,[],[f443])).

fof(f443,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | spl6_60 ),
    inference(superposition,[],[f436,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f436,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | spl6_60 ),
    inference(avatar_component_clause,[],[f435])).

fof(f437,plain,
    ( ~ spl6_60
    | spl6_1
    | ~ spl6_29
    | ~ spl6_37
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f433,f420,f278,f229,f82,f435])).

fof(f82,plain,
    ( spl6_1
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f229,plain,
    ( spl6_29
  <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f278,plain,
    ( spl6_37
  <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f420,plain,
    ( spl6_58
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f433,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | spl6_1
    | ~ spl6_29
    | ~ spl6_37
    | ~ spl6_58 ),
    inference(forward_demodulation,[],[f432,f279])).

fof(f279,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f278])).

fof(f432,plain,
    ( k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | spl6_1
    | ~ spl6_29
    | ~ spl6_58 ),
    inference(forward_demodulation,[],[f428,f230])).

fof(f230,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f229])).

fof(f428,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | spl6_1
    | ~ spl6_58 ),
    inference(superposition,[],[f83,f421])).

fof(f421,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f420])).

fof(f83,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f422,plain,
    ( spl6_58
    | ~ spl6_3
    | ~ spl6_57 ),
    inference(avatar_split_clause,[],[f418,f415,f90,f420])).

fof(f415,plain,
    ( spl6_57
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f418,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ spl6_3
    | ~ spl6_57 ),
    inference(resolution,[],[f416,f91])).

fof(f91,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f416,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) )
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f415])).

fof(f417,plain,
    ( spl6_9
    | ~ spl6_45
    | ~ spl6_4
    | spl6_57
    | ~ spl6_8
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f413,f309,f98,f102,f106,f110,f415,f94,f325,f114])).

fof(f114,plain,
    ( spl6_9
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f325,plain,
    ( spl6_45
  <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f309,plain,
    ( spl6_42
  <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f413,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
        | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)
        | v1_xboole_0(sK1) )
    | ~ spl6_42 ),
    inference(resolution,[],[f209,f310])).

fof(f310,plain,
    ( m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f309])).

fof(f209,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k8_funct_2(X4,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
      | ~ v1_funct_2(X3,X4,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,X6)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(k8_funct_2(X4,X1,X2,X3,X0),X6,X7)
      | k3_funct_2(X6,X7,k8_funct_2(X4,X1,X2,X3,X0),X5) = k1_funct_1(k8_funct_2(X4,X1,X2,X3,X0),X5)
      | v1_xboole_0(X6) ) ),
    inference(resolution,[],[f77,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(f357,plain,
    ( ~ spl6_8
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | spl6_45 ),
    inference(avatar_split_clause,[],[f355,f325,f94,f98,f102,f106,f110])).

fof(f355,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl6_45 ),
    inference(resolution,[],[f326,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f326,plain,
    ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | spl6_45 ),
    inference(avatar_component_clause,[],[f325])).

fof(f311,plain,
    ( spl6_42
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_6
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f307,f304,f102,f110,f106,f309])).

fof(f304,plain,
    ( spl6_41
  <=> ! [X3,X2] :
        ( m1_subset_1(k8_funct_2(X2,sK0,sK2,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f307,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_6
    | ~ spl6_41 ),
    inference(resolution,[],[f305,f103])).

fof(f305,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,sK0)
        | m1_subset_1(k8_funct_2(X2,sK0,sK2,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) )
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f304])).

fof(f306,plain,
    ( ~ spl6_5
    | spl6_41
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f298,f94,f304,f98])).

fof(f298,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k8_funct_2(X2,sK0,sK2,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))
        | ~ v1_funct_2(X3,X2,sK0)
        | ~ v1_funct_1(X3) )
    | ~ spl6_4 ),
    inference(resolution,[],[f79,f95])).

fof(f95,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f280,plain,
    ( spl6_37
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f276,f262,f244,f233,f278])).

fof(f233,plain,
    ( spl6_30
  <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f244,plain,
    ( spl6_32
  <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f262,plain,
    ( spl6_35
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,sK0)
        | k3_funct_2(sK0,sK2,sK4,X1) = k7_partfun1(sK2,sK4,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f276,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f275,f234])).

fof(f234,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f233])).

fof(f275,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_32
    | ~ spl6_35 ),
    inference(resolution,[],[f263,f245])).

fof(f245,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f244])).

fof(f263,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK0)
        | k3_funct_2(sK0,sK2,sK4,X1) = k7_partfun1(sK2,sK4,X1) )
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f262])).

fof(f267,plain,
    ( spl6_10
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f266,f259,f94,f86,f118])).

fof(f86,plain,
    ( spl6_2
  <=> v1_partfun1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f259,plain,
    ( spl6_34
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f266,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_4
    | ~ spl6_34 ),
    inference(resolution,[],[f265,f95])).

fof(f265,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
        | ~ v1_partfun1(X0,X1)
        | v1_xboole_0(X1) )
    | ~ spl6_34 ),
    inference(resolution,[],[f260,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f260,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f259])).

fof(f264,plain,
    ( spl6_10
    | spl6_34
    | ~ spl6_5
    | ~ spl6_21
    | spl6_35
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f252,f94,f262,f179,f98,f259,f118])).

fof(f179,plain,
    ( spl6_21
  <=> v1_funct_2(sK4,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f252,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK0)
        | k3_funct_2(sK0,sK2,sK4,X1) = k7_partfun1(sK2,sK4,X1)
        | ~ v1_funct_2(sK4,sK0,sK2)
        | ~ v1_funct_1(sK4)
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f60,f95])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

fof(f246,plain,
    ( ~ spl6_3
    | spl6_32
    | ~ spl6_23
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f237,f229,f193,f244,f90])).

fof(f193,plain,
    ( spl6_23
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f237,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ m1_subset_1(sK5,sK1)
    | ~ spl6_23
    | ~ spl6_29 ),
    inference(superposition,[],[f194,f230])).

fof(f194,plain,
    ( ! [X0] :
        ( m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f193])).

fof(f242,plain,
    ( spl6_30
    | ~ spl6_25
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f236,f229,f206,f233])).

fof(f206,plain,
    ( spl6_25
  <=> k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f236,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_25
    | ~ spl6_29 ),
    inference(superposition,[],[f207,f230])).

fof(f207,plain,
    ( k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f206])).

fof(f231,plain,
    ( spl6_29
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f227,f224,f90,f229])).

fof(f224,plain,
    ( spl6_28
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f227,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(resolution,[],[f225,f91])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f224])).

fof(f226,plain,
    ( spl6_9
    | ~ spl6_7
    | spl6_28
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f222,f110,f102,f224,f106,f114])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
        | v1_xboole_0(sK1) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(resolution,[],[f197,f103])).

fof(f197,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(X3,X4)
        | ~ v1_funct_2(sK3,X4,X5)
        | k3_funct_2(X4,X5,sK3,X3) = k1_funct_1(sK3,X3)
        | v1_xboole_0(X4) )
    | ~ spl6_8 ),
    inference(resolution,[],[f76,f111])).

fof(f111,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f208,plain,
    ( spl6_25
    | ~ spl6_3
    | ~ spl6_23
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f204,f200,f193,f90,f206])).

fof(f200,plain,
    ( spl6_24
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f204,plain,
    ( k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | ~ spl6_3
    | ~ spl6_23
    | ~ spl6_24 ),
    inference(resolution,[],[f203,f91])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0)) )
    | ~ spl6_23
    | ~ spl6_24 ),
    inference(resolution,[],[f201,f194])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,
    ( spl6_10
    | ~ spl6_21
    | spl6_24
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f198,f98,f94,f200,f179,f118])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | ~ v1_funct_2(sK4,sK0,sK2)
        | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)
        | v1_xboole_0(sK0) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(resolution,[],[f196,f95])).

fof(f196,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X0,X1)
        | ~ v1_funct_2(sK4,X1,X2)
        | k3_funct_2(X1,X2,sK4,X0) = k1_funct_1(sK4,X0)
        | v1_xboole_0(X1) )
    | ~ spl6_5 ),
    inference(resolution,[],[f76,f99])).

fof(f99,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f98])).

fof(f195,plain,
    ( spl6_9
    | ~ spl6_7
    | spl6_23
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f189,f110,f102,f193,f106,f114])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0)
        | v1_xboole_0(sK1) )
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(resolution,[],[f175,f103])).

fof(f175,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ m1_subset_1(X3,X4)
        | ~ v1_funct_2(sK3,X4,X5)
        | m1_subset_1(k3_funct_2(X4,X5,sK3,X3),X5)
        | v1_xboole_0(X4) )
    | ~ spl6_8 ),
    inference(resolution,[],[f75,f111])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f188,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_2
    | spl6_21 ),
    inference(avatar_split_clause,[],[f185,f179,f86,f98,f94])).

fof(f185,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_21 ),
    inference(resolution,[],[f180,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f180,plain,
    ( ~ v1_funct_2(sK4,sK0,sK2)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f179])).

fof(f152,plain,
    ( ~ spl6_4
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f95,f138])).

fof(f138,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl6_13
  <=> ! [X1,X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f140,plain,
    ( spl6_12
    | spl6_13
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f131,f94,f86,f137,f134])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(sK4,sK0)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | sK0 = k1_relat_1(sK4) )
    | ~ spl6_4 ),
    inference(resolution,[],[f129,f95])).

fof(f129,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_partfun1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_relat_1(X0) = X1 ) ),
    inference(resolution,[],[f128,f62])).

fof(f128,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_relat_1(X7)
      | ~ v1_partfun1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X7))
      | k1_relat_1(X4) = X5 ) ),
    inference(resolution,[],[f125,f61])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = X1
      | ~ v1_partfun1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f66,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f124,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f59,f122])).

fof(f122,plain,
    ( spl6_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f120,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f49,f118])).

fof(f49,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    & v1_partfun1(sK4,sK0)
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f19,f45,f44,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                        & v1_partfun1(X4,X0)
                        & m1_subset_1(X5,X1) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5))
                      & v1_partfun1(X4,sK0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
              & v1_funct_2(X3,X1,sK0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5))
                    & v1_partfun1(X4,sK0)
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
            & v1_funct_2(X3,X1,sK0)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X3,X2] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5))
                  & v1_partfun1(X4,sK0)
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X3,X2] :
        ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5))
                & v1_partfun1(X4,sK0)
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5))
              & v1_partfun1(X4,sK0)
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5))
            & v1_partfun1(X4,sK0)
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5))
          & v1_partfun1(sK4,sK0)
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X5] :
        ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5))
        & v1_partfun1(sK4,sK0)
        & m1_subset_1(X5,sK1) )
   => ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
      & v1_partfun1(sK4,sK0)
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

fof(f116,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f50,f114])).

fof(f50,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f112,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f51,f110])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f108,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f52,f106])).

fof(f52,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f104,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f53,f102])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f100,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f54,f98])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f55,f94])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f46])).

fof(f92,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f56,f90])).

fof(f56,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f57,f86])).

fof(f57,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f84,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f58,f82])).

fof(f58,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:32:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (9883)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (9893)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (9885)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (9891)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (9884)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (9881)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (9890)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (9892)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (9880)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (9879)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (9897)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (9898)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (9878)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (9879)Refutation not found, incomplete strategy% (9879)------------------------------
% 0.22/0.51  % (9879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9879)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9879)Memory used [KB]: 10618
% 0.22/0.51  % (9879)Time elapsed: 0.093 s
% 0.22/0.51  % (9879)------------------------------
% 0.22/0.51  % (9879)------------------------------
% 0.22/0.52  % (9886)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (9887)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (9892)Refutation not found, incomplete strategy% (9892)------------------------------
% 0.22/0.52  % (9892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9888)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (9899)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (9889)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (9892)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (9892)Memory used [KB]: 1791
% 0.22/0.52  % (9892)Time elapsed: 0.081 s
% 0.22/0.52  % (9892)------------------------------
% 0.22/0.52  % (9892)------------------------------
% 0.22/0.52  % (9885)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (9899)Refutation not found, incomplete strategy% (9899)------------------------------
% 0.22/0.52  % (9899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9899)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (9899)Memory used [KB]: 10618
% 0.22/0.52  % (9899)Time elapsed: 0.104 s
% 0.22/0.52  % (9899)------------------------------
% 0.22/0.52  % (9899)------------------------------
% 0.22/0.53  % (9894)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.53  % (9895)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f492,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f84,f88,f92,f96,f100,f104,f108,f112,f116,f120,f124,f140,f152,f188,f195,f202,f208,f226,f231,f242,f246,f264,f267,f280,f306,f311,f357,f417,f422,f437,f451,f462,f467,f475,f481,f484,f490,f491])).
% 0.22/0.53  fof(f491,plain,(
% 0.22/0.53    k1_xboole_0 != sK1 | v1_xboole_0(sK1) | ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.53  fof(f490,plain,(
% 0.22/0.53    ~spl6_6 | spl6_68),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f489])).
% 0.22/0.53  fof(f489,plain,(
% 0.22/0.53    $false | (~spl6_6 | spl6_68)),
% 0.22/0.53    inference(subsumption_resolution,[],[f103,f487])).
% 0.22/0.53  fof(f487,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl6_68),
% 0.22/0.53    inference(resolution,[],[f474,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.53  fof(f474,plain,(
% 0.22/0.53    ~v5_relat_1(sK3,sK0) | spl6_68),
% 0.22/0.53    inference(avatar_component_clause,[],[f473])).
% 0.22/0.53  fof(f473,plain,(
% 0.22/0.53    spl6_68 <=> v5_relat_1(sK3,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f102])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.53  fof(f484,plain,(
% 0.22/0.53    spl6_69),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f482])).
% 0.22/0.53  fof(f482,plain,(
% 0.22/0.53    $false | spl6_69),
% 0.22/0.53    inference(resolution,[],[f480,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.53  fof(f480,plain,(
% 0.22/0.53    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl6_69),
% 0.22/0.53    inference(avatar_component_clause,[],[f479])).
% 0.22/0.53  fof(f479,plain,(
% 0.22/0.53    spl6_69 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).
% 0.22/0.53  fof(f481,plain,(
% 0.22/0.53    ~spl6_69 | ~spl6_6 | spl6_67),
% 0.22/0.53    inference(avatar_split_clause,[],[f477,f470,f102,f479])).
% 0.22/0.53  fof(f470,plain,(
% 0.22/0.53    spl6_67 <=> v1_relat_1(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).
% 0.22/0.53  fof(f477,plain,(
% 0.22/0.53    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | (~spl6_6 | spl6_67)),
% 0.22/0.53    inference(resolution,[],[f476,f103])).
% 0.22/0.53  fof(f476,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_67),
% 0.22/0.53    inference(resolution,[],[f471,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.53  fof(f471,plain,(
% 0.22/0.53    ~v1_relat_1(sK3) | spl6_67),
% 0.22/0.53    inference(avatar_component_clause,[],[f470])).
% 0.22/0.53  fof(f475,plain,(
% 0.22/0.53    ~spl6_67 | ~spl6_68 | spl6_66),
% 0.22/0.53    inference(avatar_split_clause,[],[f468,f465,f473,f470])).
% 0.22/0.53  fof(f465,plain,(
% 0.22/0.53    spl6_66 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 0.22/0.53  fof(f468,plain,(
% 0.22/0.53    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | spl6_66),
% 0.22/0.53    inference(resolution,[],[f466,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.53  fof(f466,plain,(
% 0.22/0.53    ~r1_tarski(k2_relat_1(sK3),sK0) | spl6_66),
% 0.22/0.53    inference(avatar_component_clause,[],[f465])).
% 0.22/0.53  fof(f467,plain,(
% 0.22/0.53    ~spl6_6 | ~spl6_66 | spl6_65),
% 0.22/0.53    inference(avatar_split_clause,[],[f463,f460,f465,f102])).
% 0.22/0.53  fof(f460,plain,(
% 0.22/0.53    spl6_65 <=> r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 0.22/0.53  fof(f463,plain,(
% 0.22/0.53    ~r1_tarski(k2_relat_1(sK3),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_65),
% 0.22/0.53    inference(superposition,[],[f461,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.53  fof(f461,plain,(
% 0.22/0.53    ~r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0) | spl6_65),
% 0.22/0.53    inference(avatar_component_clause,[],[f460])).
% 0.22/0.53  fof(f462,plain,(
% 0.22/0.53    ~spl6_4 | ~spl6_65 | ~spl6_12 | spl6_62),
% 0.22/0.53    inference(avatar_split_clause,[],[f458,f446,f134,f460,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    spl6_4 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    spl6_12 <=> sK0 = k1_relat_1(sK4)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.53  fof(f446,plain,(
% 0.22/0.53    spl6_62 <=> r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 0.22/0.53  fof(f458,plain,(
% 0.22/0.53    ~r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl6_12 | spl6_62)),
% 0.22/0.53    inference(forward_demodulation,[],[f453,f135])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    sK0 = k1_relat_1(sK4) | ~spl6_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f134])).
% 0.22/0.53  fof(f453,plain,(
% 0.22/0.53    ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl6_62),
% 0.22/0.53    inference(superposition,[],[f447,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.53  fof(f447,plain,(
% 0.22/0.53    ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | spl6_62),
% 0.22/0.53    inference(avatar_component_clause,[],[f446])).
% 0.22/0.53  fof(f451,plain,(
% 0.22/0.53    spl6_10 | ~spl6_8 | ~spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_4 | ~spl6_3 | ~spl6_62 | spl6_63 | spl6_60),
% 0.22/0.53    inference(avatar_split_clause,[],[f444,f435,f449,f446,f90,f94,f98,f102,f106,f110,f118])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    spl6_10 <=> v1_xboole_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    spl6_8 <=> v1_funct_1(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    spl6_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    spl6_5 <=> v1_funct_1(sK4)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    spl6_3 <=> m1_subset_1(sK5,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.53  fof(f449,plain,(
% 0.22/0.53    spl6_63 <=> k1_xboole_0 = sK1),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 0.22/0.53  fof(f435,plain,(
% 0.22/0.53    spl6_60 <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 0.22/0.53  fof(f444,plain,(
% 0.22/0.53    k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK0) | spl6_60),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f443])).
% 0.22/0.53  fof(f443,plain,(
% 0.22/0.53    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK0) | spl6_60),
% 0.22/0.53    inference(superposition,[],[f436,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.22/0.53    inference(flattening,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.22/0.53  fof(f436,plain,(
% 0.22/0.53    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | spl6_60),
% 0.22/0.53    inference(avatar_component_clause,[],[f435])).
% 0.22/0.53  fof(f437,plain,(
% 0.22/0.53    ~spl6_60 | spl6_1 | ~spl6_29 | ~spl6_37 | ~spl6_58),
% 0.22/0.53    inference(avatar_split_clause,[],[f433,f420,f278,f229,f82,f435])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl6_1 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.53  fof(f229,plain,(
% 0.22/0.53    spl6_29 <=> k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.22/0.53  fof(f278,plain,(
% 0.22/0.53    spl6_37 <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.22/0.53  fof(f420,plain,(
% 0.22/0.53    spl6_58 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 0.22/0.53  fof(f433,plain,(
% 0.22/0.53    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | (spl6_1 | ~spl6_29 | ~spl6_37 | ~spl6_58)),
% 0.22/0.53    inference(forward_demodulation,[],[f432,f279])).
% 0.22/0.53  fof(f279,plain,(
% 0.22/0.53    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~spl6_37),
% 0.22/0.53    inference(avatar_component_clause,[],[f278])).
% 0.22/0.53  fof(f432,plain,(
% 0.22/0.53    k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | (spl6_1 | ~spl6_29 | ~spl6_58)),
% 0.22/0.53    inference(forward_demodulation,[],[f428,f230])).
% 0.22/0.53  fof(f230,plain,(
% 0.22/0.53    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | ~spl6_29),
% 0.22/0.53    inference(avatar_component_clause,[],[f229])).
% 0.22/0.53  fof(f428,plain,(
% 0.22/0.53    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | (spl6_1 | ~spl6_58)),
% 0.22/0.53    inference(superposition,[],[f83,f421])).
% 0.22/0.53  fof(f421,plain,(
% 0.22/0.53    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | ~spl6_58),
% 0.22/0.53    inference(avatar_component_clause,[],[f420])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | spl6_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f82])).
% 0.22/0.53  fof(f422,plain,(
% 0.22/0.53    spl6_58 | ~spl6_3 | ~spl6_57),
% 0.22/0.53    inference(avatar_split_clause,[],[f418,f415,f90,f420])).
% 0.22/0.53  fof(f415,plain,(
% 0.22/0.53    spl6_57 <=> ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 0.22/0.53  fof(f418,plain,(
% 0.22/0.53    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | (~spl6_3 | ~spl6_57)),
% 0.22/0.53    inference(resolution,[],[f416,f91])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    m1_subset_1(sK5,sK1) | ~spl6_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f90])).
% 0.22/0.53  fof(f416,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0)) ) | ~spl6_57),
% 0.22/0.53    inference(avatar_component_clause,[],[f415])).
% 0.22/0.53  fof(f417,plain,(
% 0.22/0.53    spl6_9 | ~spl6_45 | ~spl6_4 | spl6_57 | ~spl6_8 | ~spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_42),
% 0.22/0.53    inference(avatar_split_clause,[],[f413,f309,f98,f102,f106,f110,f415,f94,f325,f114])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    spl6_9 <=> v1_xboole_0(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.53  fof(f325,plain,(
% 0.22/0.53    spl6_45 <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.22/0.53  fof(f309,plain,(
% 0.22/0.53    spl6_42 <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.22/0.53  fof(f413,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),X0) | v1_xboole_0(sK1)) ) | ~spl6_42),
% 0.22/0.53    inference(resolution,[],[f209,f310])).
% 0.22/0.53  fof(f310,plain,(
% 0.22/0.53    m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_42),
% 0.22/0.53    inference(avatar_component_clause,[],[f309])).
% 0.22/0.53  fof(f209,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~m1_subset_1(k8_funct_2(X4,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) | ~v1_funct_2(X3,X4,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X5,X6) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k8_funct_2(X4,X1,X2,X3,X0),X6,X7) | k3_funct_2(X6,X7,k8_funct_2(X4,X1,X2,X3,X0),X5) = k1_funct_1(k8_funct_2(X4,X1,X2,X3,X0),X5) | v1_xboole_0(X6)) )),
% 0.22/0.53    inference(resolution,[],[f77,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.53    inference(flattening,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).
% 0.22/0.53  fof(f357,plain,(
% 0.22/0.53    ~spl6_8 | ~spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_4 | spl6_45),
% 0.22/0.53    inference(avatar_split_clause,[],[f355,f325,f94,f98,f102,f106,f110])).
% 0.22/0.53  fof(f355,plain,(
% 0.22/0.53    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | spl6_45),
% 0.22/0.53    inference(resolution,[],[f326,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f326,plain,(
% 0.22/0.53    ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | spl6_45),
% 0.22/0.53    inference(avatar_component_clause,[],[f325])).
% 0.22/0.53  fof(f311,plain,(
% 0.22/0.53    spl6_42 | ~spl6_7 | ~spl6_8 | ~spl6_6 | ~spl6_41),
% 0.22/0.53    inference(avatar_split_clause,[],[f307,f304,f102,f110,f106,f309])).
% 0.22/0.53  fof(f304,plain,(
% 0.22/0.53    spl6_41 <=> ! [X3,X2] : (m1_subset_1(k8_funct_2(X2,sK0,sK2,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.22/0.53  fof(f307,plain,(
% 0.22/0.53    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_6 | ~spl6_41)),
% 0.22/0.53    inference(resolution,[],[f305,f103])).
% 0.22/0.53  fof(f305,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,sK0) | m1_subset_1(k8_funct_2(X2,sK0,sK2,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))) ) | ~spl6_41),
% 0.22/0.53    inference(avatar_component_clause,[],[f304])).
% 0.22/0.53  fof(f306,plain,(
% 0.22/0.53    ~spl6_5 | spl6_41 | ~spl6_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f298,f94,f304,f98])).
% 0.22/0.53  fof(f298,plain,(
% 0.22/0.53    ( ! [X2,X3] : (m1_subset_1(k8_funct_2(X2,sK0,sK2,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) | ~v1_funct_2(X3,X2,sK0) | ~v1_funct_1(X3)) ) | ~spl6_4),
% 0.22/0.53    inference(resolution,[],[f79,f95])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f94])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f280,plain,(
% 0.22/0.53    spl6_37 | ~spl6_30 | ~spl6_32 | ~spl6_35),
% 0.22/0.53    inference(avatar_split_clause,[],[f276,f262,f244,f233,f278])).
% 0.22/0.53  fof(f233,plain,(
% 0.22/0.53    spl6_30 <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.22/0.53  fof(f244,plain,(
% 0.22/0.53    spl6_32 <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.22/0.53  fof(f262,plain,(
% 0.22/0.53    spl6_35 <=> ! [X1] : (~m1_subset_1(X1,sK0) | k3_funct_2(sK0,sK2,sK4,X1) = k7_partfun1(sK2,sK4,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.22/0.53  fof(f276,plain,(
% 0.22/0.53    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | (~spl6_30 | ~spl6_32 | ~spl6_35)),
% 0.22/0.53    inference(forward_demodulation,[],[f275,f234])).
% 0.22/0.53  fof(f234,plain,(
% 0.22/0.53    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) | ~spl6_30),
% 0.22/0.53    inference(avatar_component_clause,[],[f233])).
% 0.22/0.53  fof(f275,plain,(
% 0.22/0.53    k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | (~spl6_32 | ~spl6_35)),
% 0.22/0.53    inference(resolution,[],[f263,f245])).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~spl6_32),
% 0.22/0.53    inference(avatar_component_clause,[],[f244])).
% 0.22/0.53  fof(f263,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,sK0) | k3_funct_2(sK0,sK2,sK4,X1) = k7_partfun1(sK2,sK4,X1)) ) | ~spl6_35),
% 0.22/0.53    inference(avatar_component_clause,[],[f262])).
% 0.22/0.53  fof(f267,plain,(
% 0.22/0.53    spl6_10 | ~spl6_2 | ~spl6_4 | ~spl6_34),
% 0.22/0.53    inference(avatar_split_clause,[],[f266,f259,f94,f86,f118])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl6_2 <=> v1_partfun1(sK4,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.53  fof(f259,plain,(
% 0.22/0.53    spl6_34 <=> v1_xboole_0(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.22/0.53  fof(f266,plain,(
% 0.22/0.53    ~v1_partfun1(sK4,sK0) | v1_xboole_0(sK0) | (~spl6_4 | ~spl6_34)),
% 0.22/0.53    inference(resolution,[],[f265,f95])).
% 0.22/0.53  fof(f265,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) | ~v1_partfun1(X0,X1) | v1_xboole_0(X1)) ) | ~spl6_34),
% 0.22/0.53    inference(resolution,[],[f260,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).
% 0.22/0.53  fof(f260,plain,(
% 0.22/0.53    v1_xboole_0(sK2) | ~spl6_34),
% 0.22/0.53    inference(avatar_component_clause,[],[f259])).
% 0.22/0.53  fof(f264,plain,(
% 0.22/0.53    spl6_10 | spl6_34 | ~spl6_5 | ~spl6_21 | spl6_35 | ~spl6_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f252,f94,f262,f179,f98,f259,f118])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    spl6_21 <=> v1_funct_2(sK4,sK0,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.22/0.53  fof(f252,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(X1,sK0) | k3_funct_2(sK0,sK2,sK4,X1) = k7_partfun1(sK2,sK4,X1) | ~v1_funct_2(sK4,sK0,sK2) | ~v1_funct_1(sK4) | v1_xboole_0(sK2) | v1_xboole_0(sK0)) ) | ~spl6_4),
% 0.22/0.53    inference(resolution,[],[f60,f95])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).
% 0.22/0.53  fof(f246,plain,(
% 0.22/0.53    ~spl6_3 | spl6_32 | ~spl6_23 | ~spl6_29),
% 0.22/0.53    inference(avatar_split_clause,[],[f237,f229,f193,f244,f90])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    spl6_23 <=> ! [X0] : (~m1_subset_1(X0,sK1) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.22/0.53  fof(f237,plain,(
% 0.22/0.53    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~m1_subset_1(sK5,sK1) | (~spl6_23 | ~spl6_29)),
% 0.22/0.53    inference(superposition,[],[f194,f230])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) | ~m1_subset_1(X0,sK1)) ) | ~spl6_23),
% 0.22/0.53    inference(avatar_component_clause,[],[f193])).
% 0.22/0.53  fof(f242,plain,(
% 0.22/0.53    spl6_30 | ~spl6_25 | ~spl6_29),
% 0.22/0.53    inference(avatar_split_clause,[],[f236,f229,f206,f233])).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    spl6_25 <=> k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.22/0.53  fof(f236,plain,(
% 0.22/0.53    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) | (~spl6_25 | ~spl6_29)),
% 0.22/0.53    inference(superposition,[],[f207,f230])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | ~spl6_25),
% 0.22/0.53    inference(avatar_component_clause,[],[f206])).
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    spl6_29 | ~spl6_3 | ~spl6_28),
% 0.22/0.53    inference(avatar_split_clause,[],[f227,f224,f90,f229])).
% 0.22/0.53  fof(f224,plain,(
% 0.22/0.53    spl6_28 <=> ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    k3_funct_2(sK1,sK0,sK3,sK5) = k1_funct_1(sK3,sK5) | (~spl6_3 | ~spl6_28)),
% 0.22/0.53    inference(resolution,[],[f225,f91])).
% 0.22/0.53  fof(f225,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)) ) | ~spl6_28),
% 0.22/0.53    inference(avatar_component_clause,[],[f224])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    spl6_9 | ~spl6_7 | spl6_28 | ~spl6_6 | ~spl6_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f222,f110,f102,f224,f106,f114])).
% 0.22/0.53  fof(f222,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK0) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) | v1_xboole_0(sK1)) ) | (~spl6_6 | ~spl6_8)),
% 0.22/0.53    inference(resolution,[],[f197,f103])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(X3,X4) | ~v1_funct_2(sK3,X4,X5) | k3_funct_2(X4,X5,sK3,X3) = k1_funct_1(sK3,X3) | v1_xboole_0(X4)) ) | ~spl6_8),
% 0.22/0.53    inference(resolution,[],[f76,f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    v1_funct_1(sK3) | ~spl6_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f110])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    spl6_25 | ~spl6_3 | ~spl6_23 | ~spl6_24),
% 0.22/0.53    inference(avatar_split_clause,[],[f204,f200,f193,f90,f206])).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    spl6_24 <=> ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | (~spl6_3 | ~spl6_23 | ~spl6_24)),
% 0.22/0.53    inference(resolution,[],[f203,f91])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK0,sK2,sK4,k3_funct_2(sK1,sK0,sK3,X0)) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X0))) ) | (~spl6_23 | ~spl6_24)),
% 0.22/0.53    inference(resolution,[],[f201,f194])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0)) ) | ~spl6_24),
% 0.22/0.53    inference(avatar_component_clause,[],[f200])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    spl6_10 | ~spl6_21 | spl6_24 | ~spl6_4 | ~spl6_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f198,f98,f94,f200,f179,f118])).
% 0.22/0.53  fof(f198,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,sK0) | ~v1_funct_2(sK4,sK0,sK2) | k3_funct_2(sK0,sK2,sK4,X0) = k1_funct_1(sK4,X0) | v1_xboole_0(sK0)) ) | (~spl6_4 | ~spl6_5)),
% 0.22/0.53    inference(resolution,[],[f196,f95])).
% 0.22/0.53  fof(f196,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,X1) | ~v1_funct_2(sK4,X1,X2) | k3_funct_2(X1,X2,sK4,X0) = k1_funct_1(sK4,X0) | v1_xboole_0(X1)) ) | ~spl6_5),
% 0.22/0.53    inference(resolution,[],[f76,f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    v1_funct_1(sK4) | ~spl6_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f98])).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    spl6_9 | ~spl6_7 | spl6_23 | ~spl6_6 | ~spl6_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f189,f110,f102,f193,f106,f114])).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK0) | m1_subset_1(k3_funct_2(sK1,sK0,sK3,X0),sK0) | v1_xboole_0(sK1)) ) | (~spl6_6 | ~spl6_8)),
% 0.22/0.53    inference(resolution,[],[f175,f103])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~m1_subset_1(X3,X4) | ~v1_funct_2(sK3,X4,X5) | m1_subset_1(k3_funct_2(X4,X5,sK3,X3),X5) | v1_xboole_0(X4)) ) | ~spl6_8),
% 0.22/0.53    inference(resolution,[],[f75,f111])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    ~spl6_4 | ~spl6_5 | ~spl6_2 | spl6_21),
% 0.22/0.53    inference(avatar_split_clause,[],[f185,f179,f86,f98,f94])).
% 0.22/0.53  fof(f185,plain,(
% 0.22/0.53    ~v1_partfun1(sK4,sK0) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl6_21),
% 0.22/0.53    inference(resolution,[],[f180,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(flattening,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    ~v1_funct_2(sK4,sK0,sK2) | spl6_21),
% 0.22/0.53    inference(avatar_component_clause,[],[f179])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    ~spl6_4 | ~spl6_13),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f151])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    $false | (~spl6_4 | ~spl6_13)),
% 0.22/0.53    inference(subsumption_resolution,[],[f95,f138])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f137])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    spl6_13 <=> ! [X1,X0] : ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    spl6_12 | spl6_13 | ~spl6_2 | ~spl6_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f131,f94,f86,f137,f134])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_partfun1(sK4,sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK0 = k1_relat_1(sK4)) ) | ~spl6_4),
% 0.22/0.53    inference(resolution,[],[f129,f95])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_relat_1(X0) = X1) )),
% 0.22/0.53    inference(resolution,[],[f128,f62])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    ( ! [X6,X4,X7,X5] : (~v1_relat_1(X7) | ~v1_partfun1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(X4,k1_zfmisc_1(X7)) | k1_relat_1(X4) = X5) )),
% 0.22/0.53    inference(resolution,[],[f125,f61])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.53    inference(resolution,[],[f66,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    spl6_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f59,f122])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    spl6_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    ~spl6_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f49,f118])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ~v1_xboole_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f19,f45,f44,f43,f42,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ? [X4] : (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(sK4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(sK4,sK0) & m1_subset_1(X5,sK1)) => (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f16])).
% 0.22/0.53  fof(f16,conjecture,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    ~spl6_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f50,f114])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ~v1_xboole_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    spl6_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f51,f110])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    v1_funct_1(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    spl6_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f52,f106])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    spl6_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f53,f102])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    spl6_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f54,f98])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    v1_funct_1(sK4)),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    spl6_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f55,f94])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    spl6_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f56,f90])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    m1_subset_1(sK5,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    spl6_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f57,f86])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    v1_partfun1(sK4,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ~spl6_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f58,f82])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (9885)------------------------------
% 0.22/0.53  % (9885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9885)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (9885)Memory used [KB]: 11129
% 0.22/0.53  % (9885)Time elapsed: 0.045 s
% 0.22/0.53  % (9885)------------------------------
% 0.22/0.53  % (9885)------------------------------
% 1.40/0.54  % (9875)Success in time 0.173 s
%------------------------------------------------------------------------------
