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
% DateTime   : Thu Dec  3 13:08:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 282 expanded)
%              Number of leaves         :   39 ( 140 expanded)
%              Depth                    :   11
%              Number of atoms          :  550 (1794 expanded)
%              Number of equality atoms :   63 ( 212 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f82,f86,f90,f94,f98,f102,f106,f123,f125,f127,f140,f182,f194,f205,f210,f212,f218,f219])).

fof(f219,plain,
    ( k1_xboole_0 != sK1
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f218,plain,
    ( ~ spl6_3
    | ~ spl6_15
    | spl6_19 ),
    inference(avatar_split_clause,[],[f217,f192,f138,f72])).

fof(f72,plain,
    ( spl6_3
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f138,plain,
    ( spl6_15
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f192,plain,
    ( spl6_19
  <=> k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f217,plain,
    ( ~ m1_subset_1(sK5,sK1)
    | ~ spl6_15
    | spl6_19 ),
    inference(trivial_inequality_removal,[],[f216])).

fof(f216,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(sK5,sK1)
    | ~ spl6_15
    | spl6_19 ),
    inference(superposition,[],[f193,f139])).

fof(f139,plain,
    ( ! [X0] :
        ( k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f138])).

fof(f193,plain,
    ( k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f212,plain,
    ( ~ spl6_6
    | spl6_22 ),
    inference(avatar_split_clause,[],[f211,f208,f84])).

fof(f84,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f208,plain,
    ( spl6_22
  <=> m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f211,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_22 ),
    inference(resolution,[],[f209,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f209,plain,
    ( ~ m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f208])).

fof(f210,plain,
    ( ~ spl6_22
    | spl6_21 ),
    inference(avatar_split_clause,[],[f206,f203,f208])).

fof(f203,plain,
    ( spl6_21
  <=> r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f206,plain,
    ( ~ m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))
    | spl6_21 ),
    inference(resolution,[],[f204,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f204,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f203])).

fof(f205,plain,
    ( ~ spl6_4
    | ~ spl6_21
    | ~ spl6_12
    | spl6_17 ),
    inference(avatar_split_clause,[],[f201,f186,f115,f203,f76])).

fof(f76,plain,
    ( spl6_4
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f115,plain,
    ( spl6_12
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f186,plain,
    ( spl6_17
  <=> r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f201,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_12
    | spl6_17 ),
    inference(forward_demodulation,[],[f196,f116])).

fof(f116,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f115])).

fof(f196,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_17 ),
    inference(superposition,[],[f187,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f187,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f186])).

fof(f194,plain,
    ( spl6_10
    | ~ spl6_8
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_17
    | spl6_18
    | ~ spl6_19
    | spl6_16 ),
    inference(avatar_split_clause,[],[f183,f180,f192,f189,f186,f72,f76,f80,f84,f88,f92,f100])).

fof(f100,plain,
    ( spl6_10
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f92,plain,
    ( spl6_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f88,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f80,plain,
    ( spl6_5
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f189,plain,
    ( spl6_18
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f180,plain,
    ( spl6_16
  <=> k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f183,plain,
    ( k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | spl6_16 ),
    inference(superposition,[],[f181,f54])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f181,plain,
    ( k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( spl6_9
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_3
    | ~ spl6_8
    | ~ spl6_7
    | ~ spl6_16
    | spl6_1 ),
    inference(avatar_split_clause,[],[f174,f64,f180,f88,f92,f72,f80,f84,f76,f96])).

fof(f96,plain,
    ( spl6_9
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f64,plain,
    ( spl6_1
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f174,plain,
    ( k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | v1_xboole_0(sK1)
    | spl6_1 ),
    inference(superposition,[],[f65,f173])).

fof(f173,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X3,X1)
      | ~ v1_funct_1(X4)
      | k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f167,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(f167,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k8_funct_2(X2,X3,X5,X1,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X1,X2,X3)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X4,X2)
      | ~ v1_funct_1(X0)
      | k3_funct_2(X2,X5,k8_funct_2(X2,X3,X5,X1,X0),X4) = k1_funct_1(k8_funct_2(X2,X3,X5,X1,X0),X4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
      | v1_xboole_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X1,X2,X3)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X4,X2)
      | ~ m1_subset_1(k8_funct_2(X2,X3,X5,X1,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X5)))
      | k3_funct_2(X2,X5,k8_funct_2(X2,X3,X5,X1,X0),X4) = k1_funct_1(k8_funct_2(X2,X3,X5,X1,X0),X4)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X5)))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X1,X2,X3)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f145,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f145,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(k8_funct_2(X4,X1,X2,X3,X0))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
      | ~ v1_funct_2(X3,X4,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X5,X4)
      | ~ m1_subset_1(k8_funct_2(X4,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
      | k3_funct_2(X4,X2,k8_funct_2(X4,X1,X2,X3,X0),X5) = k1_funct_1(k8_funct_2(X4,X1,X2,X3,X0),X5)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_xboole_0(X4) ) ),
    inference(resolution,[],[f60,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f140,plain,
    ( spl6_9
    | ~ spl6_8
    | ~ spl6_6
    | spl6_15
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f133,f88,f138,f84,f92,f96])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0)
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(sK1) )
    | ~ spl6_7 ),
    inference(resolution,[],[f58,f89])).

fof(f89,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f127,plain,
    ( ~ spl6_4
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f77,f122])).

fof(f122,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl6_14
  <=> ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f77,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f125,plain,
    ( ~ spl6_4
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f77,f119])).

fof(f119,plain,
    ( ! [X2,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_13
  <=> ! [X1,X2] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f123,plain,
    ( spl6_12
    | spl6_13
    | spl6_14
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f112,f68,f121,f118,f115])).

fof(f68,plain,
    ( spl6_2
  <=> v1_partfun1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f112,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | sK0 = k1_relat_1(sK4) )
    | ~ spl6_2 ),
    inference(resolution,[],[f110,f69])).

fof(f69,plain,
    ( v1_partfun1(sK4,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f110,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_partfun1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_relat_1(X0) = X1 ) ),
    inference(resolution,[],[f109,f50])).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f109,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_relat_1(X7)
      | ~ v1_partfun1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X7))
      | k1_relat_1(X4) = X5 ) ),
    inference(resolution,[],[f107,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = X1
      | ~ v1_partfun1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f51,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f106,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f48,f104])).

fof(f104,plain,
    ( spl6_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f102,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f38,f100])).

fof(f38,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    & v1_partfun1(sK4,sK0)
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f35,f34,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
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
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,sK0,X3,X5))
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

fof(f32,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,sK0,X3,X5))
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
                  ( k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,sK0,X3,X5))
                  & v1_partfun1(X4,sK0)
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3,X2] :
        ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,sK0,X3,X5))
                & v1_partfun1(X4,sK0)
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,sK0,sK3,X5))
              & v1_partfun1(X4,sK0)
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,sK0,sK3,X5))
            & v1_partfun1(X4,sK0)
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X5))
          & v1_partfun1(sK4,sK0)
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X5] :
        ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X5))
        & v1_partfun1(sK4,sK0)
        & m1_subset_1(X5,sK1) )
   => ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))
      & v1_partfun1(sK4,sK0)
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).

fof(f98,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f39,f96])).

fof(f39,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f40,f92])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f41,f88])).

fof(f41,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f42,f84])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f43,f80])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f44,f76])).

fof(f44,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f45,f72])).

fof(f45,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f46,f68])).

fof(f46,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f47,f64])).

fof(f47,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:16:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (15724)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (15715)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (15723)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (15716)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (15717)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (15714)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (15713)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (15711)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (15728)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (15721)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (15723)Refutation not found, incomplete strategy% (15723)------------------------------
% 0.21/0.51  % (15723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15723)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15723)Memory used [KB]: 1791
% 0.21/0.51  % (15723)Time elapsed: 0.038 s
% 0.21/0.51  % (15723)------------------------------
% 0.21/0.51  % (15723)------------------------------
% 0.21/0.51  % (15722)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (15716)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f82,f86,f90,f94,f98,f102,f106,f123,f125,f127,f140,f182,f194,f205,f210,f212,f218,f219])).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    k1_xboole_0 != sK1 | v1_xboole_0(sK1) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    ~spl6_3 | ~spl6_15 | spl6_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f217,f192,f138,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl6_3 <=> m1_subset_1(sK5,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    spl6_15 <=> ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    spl6_19 <=> k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    ~m1_subset_1(sK5,sK1) | (~spl6_15 | spl6_19)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f216])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(sK5,sK1) | (~spl6_15 | spl6_19)),
% 0.21/0.51    inference(superposition,[],[f193,f139])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ( ! [X0] : (k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) | ~m1_subset_1(X0,sK1)) ) | ~spl6_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f138])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl6_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f192])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    ~spl6_6 | spl6_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f211,f208,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    spl6_22 <=> m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_22),
% 0.21/0.51    inference(resolution,[],[f209,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    ~m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0)) | spl6_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f208])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ~spl6_22 | spl6_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f206,f203,f208])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    spl6_21 <=> r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    ~m1_subset_1(k2_relset_1(sK1,sK0,sK3),k1_zfmisc_1(sK0)) | spl6_21),
% 0.21/0.51    inference(resolution,[],[f204,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    ~r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0) | spl6_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f203])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    ~spl6_4 | ~spl6_21 | ~spl6_12 | spl6_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f201,f186,f115,f203,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl6_4 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    spl6_12 <=> sK0 = k1_relat_1(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    spl6_17 <=> r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    ~r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl6_12 | spl6_17)),
% 0.21/0.51    inference(forward_demodulation,[],[f196,f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK4) | ~spl6_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f115])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl6_17),
% 0.21/0.51    inference(superposition,[],[f187,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | spl6_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f186])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    spl6_10 | ~spl6_8 | ~spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_4 | ~spl6_3 | ~spl6_17 | spl6_18 | ~spl6_19 | spl6_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f183,f180,f192,f189,f186,f72,f76,f80,f84,f88,f92,f100])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl6_10 <=> v1_xboole_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    spl6_8 <=> v1_funct_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl6_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl6_5 <=> v1_funct_1(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    spl6_18 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    spl6_16 <=> k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relset_1(sK0,sK2,sK4)) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK0) | spl6_16),
% 0.21/0.51    inference(superposition,[],[f181,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | spl6_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f180])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    spl6_9 | ~spl6_4 | ~spl6_6 | ~spl6_5 | ~spl6_3 | ~spl6_8 | ~spl6_7 | ~spl6_16 | spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f174,f64,f180,f88,f92,f72,f80,f84,f76,f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl6_9 <=> v1_xboole_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl6_1 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK5,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | v1_xboole_0(sK1) | spl6_1),
% 0.21/0.51    inference(superposition,[],[f65,f173])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~m1_subset_1(X3,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5))) | v1_xboole_0(X1)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f172])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~m1_subset_1(X3,X1) | ~v1_funct_1(X4) | k3_funct_2(X1,X5,k8_funct_2(X1,X2,X5,X0,X4),X3) = k1_funct_1(k8_funct_2(X1,X2,X5,X0,X4),X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5))) | v1_xboole_0(X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X5))) | ~v1_funct_1(X4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f167,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_funct_2)).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k8_funct_2(X2,X3,X5,X1,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X5))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X1,X2,X3) | ~v1_funct_1(X1) | ~m1_subset_1(X4,X2) | ~v1_funct_1(X0) | k3_funct_2(X2,X5,k8_funct_2(X2,X3,X5,X1,X0),X4) = k1_funct_1(k8_funct_2(X2,X3,X5,X1,X0),X4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X5))) | v1_xboole_0(X2)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f166])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X1,X2,X3) | ~v1_funct_1(X1) | ~m1_subset_1(X4,X2) | ~m1_subset_1(k8_funct_2(X2,X3,X5,X1,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X5))) | k3_funct_2(X2,X5,k8_funct_2(X2,X3,X5,X1,X0),X4) = k1_funct_1(k8_funct_2(X2,X3,X5,X1,X0),X4) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X5))) | v1_xboole_0(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X5))) | ~v1_funct_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X1,X2,X3) | ~v1_funct_1(X1)) )),
% 0.21/0.51    inference(resolution,[],[f145,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(k8_funct_2(X4,X1,X2,X3,X0)) | ~v1_funct_1(X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) | ~v1_funct_2(X3,X4,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X5,X4) | ~m1_subset_1(k8_funct_2(X4,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) | k3_funct_2(X4,X2,k8_funct_2(X4,X1,X2,X3,X0),X5) = k1_funct_1(k8_funct_2(X4,X1,X2,X3,X0),X5) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_xboole_0(X4)) )),
% 0.21/0.51    inference(resolution,[],[f60,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | spl6_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f64])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    spl6_9 | ~spl6_8 | ~spl6_6 | spl6_15 | ~spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f133,f88,f138,f84,f92,f96])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k3_funct_2(sK1,sK0,sK3,X0) = k1_funct_1(sK3,X0) | ~v1_funct_1(sK3) | v1_xboole_0(sK1)) ) | ~spl6_7),
% 0.21/0.51    inference(resolution,[],[f58,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK1,sK0) | ~spl6_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f88])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ~spl6_4 | ~spl6_14),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f126])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    $false | (~spl6_4 | ~spl6_14)),
% 0.21/0.51    inference(subsumption_resolution,[],[f77,f122])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))) ) | ~spl6_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f121])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl6_14 <=> ! [X0] : ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f76])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ~spl6_4 | ~spl6_13),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f124])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    $false | (~spl6_4 | ~spl6_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f77,f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl6_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl6_13 <=> ! [X1,X2] : ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    spl6_12 | spl6_13 | spl6_14 | ~spl6_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f112,f68,f121,f118,f115])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    spl6_2 <=> v1_partfun1(sK4,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | sK0 = k1_relat_1(sK4)) ) | ~spl6_2),
% 0.21/0.51    inference(resolution,[],[f110,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    v1_partfun1(sK4,sK0) | ~spl6_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f68])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_relat_1(X0) = X1) )),
% 0.21/0.51    inference(resolution,[],[f109,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ( ! [X6,X4,X7,X5] : (~v1_relat_1(X7) | ~v1_partfun1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~m1_subset_1(X4,k1_zfmisc_1(X7)) | k1_relat_1(X4) = X5) )),
% 0.21/0.51    inference(resolution,[],[f107,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.51    inference(resolution,[],[f51,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl6_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl6_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ~spl6_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f38,f100])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ~v1_xboole_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f35,f34,f33,f32,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ? [X4] : (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k1_funct_1(X4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(sK4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(sK4,sK0) & m1_subset_1(X5,sK1)) => (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f12])).
% 0.21/0.51  fof(f12,conjecture,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k1_funct_1(X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_funct_2)).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ~spl6_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f39,f96])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ~v1_xboole_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl6_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f40,f92])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f41,f88])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl6_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f84])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl6_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f43,f80])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    v1_funct_1(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl6_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f76])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f72])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    m1_subset_1(sK5,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl6_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f68])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    v1_partfun1(sK4,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ~spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f64])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (15716)------------------------------
% 0.21/0.51  % (15716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15716)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (15716)Memory used [KB]: 10874
% 0.21/0.51  % (15716)Time elapsed: 0.044 s
% 0.21/0.51  % (15716)------------------------------
% 0.21/0.51  % (15716)------------------------------
% 0.21/0.51  % (15730)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (15712)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (15709)Success in time 0.153 s
%------------------------------------------------------------------------------
