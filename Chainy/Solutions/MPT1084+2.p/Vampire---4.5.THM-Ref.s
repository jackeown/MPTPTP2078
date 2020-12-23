%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1084+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:05 EST 2020

% Result     : Theorem 16.67s
% Output     : Refutation 16.67s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 162 expanded)
%              Number of leaves         :   23 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  315 ( 624 expanded)
%              Number of equality atoms :   61 ( 114 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3227,f3232,f3237,f3242,f3338,f3496,f3506,f3773,f3967,f4473,f4937,f8286,f8288])).

fof(f8288,plain,
    ( sK1 != k6_partfun1(sK0)
    | r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0))
    | ~ r2_funct_2(sK0,sK0,sK1,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f8286,plain,
    ( ~ spl112_109
    | spl112_240 ),
    inference(avatar_split_clause,[],[f8283,f4934,f3964])).

fof(f3964,plain,
    ( spl112_109
  <=> r2_hidden(sK99(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl112_109])])).

fof(f4934,plain,
    ( spl112_240
  <=> m1_subset_1(sK99(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl112_240])])).

fof(f8283,plain,
    ( ~ r2_hidden(sK99(sK0,sK1),sK0)
    | spl112_240 ),
    inference(resolution,[],[f4936,f2974])).

fof(f2974,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f2151])).

fof(f2151,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f4936,plain,
    ( ~ m1_subset_1(sK99(sK0,sK1),sK0)
    | spl112_240 ),
    inference(avatar_component_clause,[],[f4934])).

fof(f4937,plain,
    ( ~ spl112_13
    | ~ spl112_5
    | spl112_98
    | ~ spl112_240
    | ~ spl112_70 ),
    inference(avatar_split_clause,[],[f4932,f3756,f4934,f3917,f3239,f3348])).

fof(f3348,plain,
    ( spl112_13
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl112_13])])).

fof(f3239,plain,
    ( spl112_5
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl112_5])])).

fof(f3917,plain,
    ( spl112_98
  <=> sK1 = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl112_98])])).

fof(f3756,plain,
    ( spl112_70
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl112_70])])).

fof(f4932,plain,
    ( ~ m1_subset_1(sK99(sK0,sK1),sK0)
    | sK1 = k6_partfun1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl112_70 ),
    inference(forward_demodulation,[],[f4931,f3758])).

fof(f3758,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl112_70 ),
    inference(avatar_component_clause,[],[f3756])).

fof(f4931,plain,
    ( sK1 = k6_partfun1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ m1_subset_1(sK99(k1_relat_1(sK1),sK1),sK0)
    | ~ spl112_70 ),
    inference(forward_demodulation,[],[f4712,f3758])).

fof(f4712,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_partfun1(k1_relat_1(sK1))
    | ~ m1_subset_1(sK99(k1_relat_1(sK1),sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f4711])).

fof(f4711,plain,
    ( sK99(k1_relat_1(sK1),sK1) != sK99(k1_relat_1(sK1),sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_partfun1(k1_relat_1(sK1))
    | ~ m1_subset_1(sK99(k1_relat_1(sK1),sK1),sK0) ),
    inference(superposition,[],[f3200,f3629])).

fof(f3629,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,X1) = X1
      | ~ m1_subset_1(X1,sK0) ) ),
    inference(global_subsumption,[],[f2196,f2194,f2193,f2192,f3628])).

fof(f3628,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,X1) = X1
      | ~ m1_subset_1(X1,sK0)
      | ~ v1_funct_1(sK1)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | v1_xboole_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f3617])).

fof(f3617,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,X1) = X1
      | ~ m1_subset_1(X1,sK0)
      | ~ v1_funct_1(sK1)
      | ~ v1_funct_2(sK1,sK0,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ m1_subset_1(X1,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(superposition,[],[f2191,f2218])).

fof(f2218,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1745])).

fof(f1745,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1744])).

fof(f1744,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1555])).

fof(f1555,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f2191,plain,(
    ! [X2] :
      ( k3_funct_2(sK0,sK0,sK1,X2) = X2
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(cnf_transformation,[],[f1716])).

fof(f1716,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1715])).

fof(f1715,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_funct_2(X0,X0,X1,k6_partfun1(X0))
          & ! [X2] :
              ( k3_funct_2(X0,X0,X1,X2) = X2
              | ~ m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1648])).

fof(f1648,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X1,X0,X0)
              & v1_funct_1(X1) )
           => ( ! [X2] :
                  ( m1_subset_1(X2,X0)
                 => k3_funct_2(X0,X0,X1,X2) = X2 )
             => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1647])).

fof(f1647,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,X0)
               => k3_funct_2(X0,X0,X1,X2) = X2 )
           => r2_funct_2(X0,X0,X1,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_funct_2)).

fof(f2192,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f1716])).

fof(f2193,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f1716])).

fof(f2194,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f1716])).

fof(f2196,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f1716])).

fof(f3200,plain,(
    ! [X1] :
      ( sK99(k1_relat_1(X1),X1) != k1_funct_1(X1,sK99(k1_relat_1(X1),X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_partfun1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f3090])).

fof(f3090,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK99(X0,X1) != k1_funct_1(X1,sK99(X0,X1))
      | k6_partfun1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f2928,f2217])).

fof(f2217,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f1558])).

fof(f1558,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f2928,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK99(X0,X1) != k1_funct_1(X1,sK99(X0,X1))
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2122])).

fof(f2122,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2121])).

fof(f2121,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1010])).

fof(f1010,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f4473,plain,(
    spl112_46 ),
    inference(avatar_contradiction_clause,[],[f4471])).

fof(f4471,plain,
    ( $false
    | spl112_46 ),
    inference(resolution,[],[f3505,f2243])).

fof(f2243,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f696])).

fof(f696,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f3505,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | spl112_46 ),
    inference(avatar_component_clause,[],[f3503])).

fof(f3503,plain,
    ( spl112_46
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl112_46])])).

fof(f3967,plain,
    ( spl112_98
    | ~ spl112_13
    | ~ spl112_5
    | spl112_109
    | ~ spl112_70 ),
    inference(avatar_split_clause,[],[f3830,f3756,f3964,f3239,f3348,f3917])).

fof(f3830,plain,
    ( r2_hidden(sK99(sK0,sK1),sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_partfun1(sK0)
    | ~ spl112_70 ),
    inference(superposition,[],[f3201,f3758])).

fof(f3201,plain,(
    ! [X1] :
      ( r2_hidden(sK99(k1_relat_1(X1),X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k6_partfun1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f3091])).

fof(f3091,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK99(X0,X1),X0)
      | k6_partfun1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f2927,f2217])).

fof(f2927,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK99(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2122])).

fof(f3773,plain,
    ( ~ spl112_3
    | spl112_70
    | ~ spl112_10 ),
    inference(avatar_split_clause,[],[f3752,f3335,f3756,f3229])).

fof(f3229,plain,
    ( spl112_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl112_3])])).

fof(f3335,plain,
    ( spl112_10
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl112_10])])).

fof(f3752,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl112_10 ),
    inference(superposition,[],[f2632,f3337])).

fof(f3337,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl112_10 ),
    inference(avatar_component_clause,[],[f3335])).

fof(f2632,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1886])).

fof(f1886,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f3506,plain,
    ( spl112_13
    | ~ spl112_46
    | ~ spl112_3 ),
    inference(avatar_split_clause,[],[f3303,f3229,f3503,f3348])).

fof(f3303,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1)
    | ~ spl112_3 ),
    inference(resolution,[],[f3231,f2234])).

fof(f2234,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1761])).

fof(f1761,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f3231,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl112_3 ),
    inference(avatar_component_clause,[],[f3229])).

fof(f3496,plain,
    ( spl112_44
    | ~ spl112_5
    | ~ spl112_4
    | ~ spl112_3 ),
    inference(avatar_split_clause,[],[f3299,f3229,f3234,f3239,f3493])).

fof(f3493,plain,
    ( spl112_44
  <=> r2_funct_2(sK0,sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl112_44])])).

fof(f3234,plain,
    ( spl112_4
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl112_4])])).

fof(f3299,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | r2_funct_2(sK0,sK0,sK1,sK1)
    | ~ spl112_3 ),
    inference(resolution,[],[f3231,f3216])).

fof(f3216,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f3127])).

fof(f3127,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f2197])).

fof(f2197,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f1718])).

fof(f1718,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f1717])).

fof(f1717,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1561])).

fof(f1561,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f3338,plain,
    ( spl112_10
    | ~ spl112_5
    | ~ spl112_4
    | ~ spl112_3 ),
    inference(avatar_split_clause,[],[f3246,f3229,f3234,f3239,f3335])).

fof(f3246,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl112_3 ),
    inference(resolution,[],[f3231,f2633])).

fof(f2633,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f1888])).

fof(f1888,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f1887])).

fof(f1887,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1691])).

fof(f1691,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f3242,plain,(
    spl112_5 ),
    inference(avatar_split_clause,[],[f2192,f3239])).

fof(f3237,plain,(
    spl112_4 ),
    inference(avatar_split_clause,[],[f2193,f3234])).

fof(f3232,plain,(
    spl112_3 ),
    inference(avatar_split_clause,[],[f2194,f3229])).

fof(f3227,plain,(
    ~ spl112_2 ),
    inference(avatar_split_clause,[],[f2195,f3224])).

fof(f3224,plain,
    ( spl112_2
  <=> r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl112_2])])).

fof(f2195,plain,(
    ~ r2_funct_2(sK0,sK0,sK1,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f1716])).
%------------------------------------------------------------------------------
