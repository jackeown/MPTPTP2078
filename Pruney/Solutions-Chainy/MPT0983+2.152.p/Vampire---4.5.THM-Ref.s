%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:57 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 838 expanded)
%              Number of leaves         :   31 ( 264 expanded)
%              Depth                    :   22
%              Number of atoms          :  586 (5592 expanded)
%              Number of equality atoms :   93 ( 206 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f922,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f521,f534,f547,f656,f689,f701,f790,f872,f921])).

fof(f921,plain,
    ( ~ spl4_12
    | ~ spl4_17
    | spl4_32 ),
    inference(avatar_contradiction_clause,[],[f920])).

fof(f920,plain,
    ( $false
    | ~ spl4_12
    | ~ spl4_17
    | spl4_32 ),
    inference(subsumption_resolution,[],[f837,f802])).

fof(f802,plain,
    ( k1_xboole_0 != sK2
    | spl4_32 ),
    inference(avatar_component_clause,[],[f801])).

fof(f801,plain,
    ( spl4_32
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f837,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f836,f120])).

fof(f120,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f118,f71])).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f118,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f70,f53])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f836,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(trivial_inequality_removal,[],[f822])).

fof(f822,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(superposition,[],[f66,f791])).

fof(f791,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_12
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f546,f502])).

fof(f502,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl4_12
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f546,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f544])).

fof(f544,plain,
    ( spl4_17
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f872,plain,
    ( spl4_1
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f871])).

fof(f871,plain,
    ( $false
    | spl4_1
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f859,f112])).

fof(f112,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f92,f90])).

fof(f90,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f60,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f59,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f92,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f63,f60])).

fof(f63,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f859,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl4_1
    | ~ spl4_32 ),
    inference(backward_demodulation,[],[f105,f803])).

fof(f803,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f801])).

fof(f105,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f790,plain,
    ( ~ spl4_12
    | spl4_16 ),
    inference(avatar_contradiction_clause,[],[f789])).

fof(f789,plain,
    ( $false
    | ~ spl4_12
    | spl4_16 ),
    inference(subsumption_resolution,[],[f788,f120])).

fof(f788,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_12
    | spl4_16 ),
    inference(subsumption_resolution,[],[f787,f565])).

fof(f565,plain,
    ( v4_relat_1(sK2,k1_xboole_0)
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f189,f502])).

fof(f189,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f81,f53])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f787,plain,
    ( ~ v4_relat_1(sK2,k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | ~ spl4_12
    | spl4_16 ),
    inference(resolution,[],[f773,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f773,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_xboole_0)
    | ~ spl4_12
    | spl4_16 ),
    inference(forward_demodulation,[],[f542,f502])).

fof(f542,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f540])).

fof(f540,plain,
    ( spl4_16
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f701,plain,
    ( spl4_12
    | ~ spl4_13
    | spl4_1 ),
    inference(avatar_split_clause,[],[f498,f103,f504,f500])).

fof(f504,plain,
    ( spl4_13
  <=> v2_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f498,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | spl4_1 ),
    inference(subsumption_resolution,[],[f497,f51])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f497,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f496,f52])).

fof(f52,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f496,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f495,f53])).

fof(f495,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f494,f54])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f494,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f493,f55])).

fof(f55,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f493,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f492,f56])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f492,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f483,f105])).

fof(f483,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f83,f409])).

fof(f409,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f405,f51])).

fof(f405,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f269,f53])).

fof(f269,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | k1_partfun1(X10,X11,sK1,sK0,X12,sK3) = k5_relat_1(X12,sK3)
      | ~ v1_funct_1(X12) ) ),
    inference(subsumption_resolution,[],[f259,f54])).

fof(f259,plain,(
    ! [X12,X10,X11] :
      ( k1_partfun1(X10,X11,sK1,sK0,X12,sK3) = k5_relat_1(X12,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X12) ) ),
    inference(resolution,[],[f87,f56])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

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
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f689,plain,
    ( spl4_2
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f688])).

fof(f688,plain,
    ( $false
    | spl4_2
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f687,f121])).

fof(f121,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f119,f71])).

fof(f119,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f70,f56])).

fof(f687,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_2
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f679,f109])).

fof(f109,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f679,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_15 ),
    inference(superposition,[],[f202,f533])).

fof(f533,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f531])).

fof(f531,plain,
    ( spl4_15
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f202,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f96,f155])).

fof(f155,plain,(
    ! [X2] :
      ( v5_relat_1(X2,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f75,f97])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f96,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f656,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f655])).

fof(f655,plain,
    ( $false
    | spl4_14 ),
    inference(subsumption_resolution,[],[f654,f121])).

fof(f654,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_14 ),
    inference(subsumption_resolution,[],[f653,f199])).

fof(f199,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f82,f56])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f653,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | spl4_14 ),
    inference(resolution,[],[f529,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f529,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f527])).

fof(f527,plain,
    ( spl4_14
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f547,plain,
    ( ~ spl4_16
    | spl4_17 ),
    inference(avatar_split_clause,[],[f538,f544,f540])).

fof(f538,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(forward_demodulation,[],[f537,f95])).

fof(f95,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f64,f60])).

fof(f64,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f537,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f536,f95])).

fof(f536,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f535,f121])).

fof(f535,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f515,f120])).

fof(f515,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0)))
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f208,f509])).

fof(f509,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f487,f508])).

fof(f508,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f480,f247])).

fof(f247,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X1,X1,X2,k6_partfun1(X1))
      | k6_partfun1(X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) ) ),
    inference(resolution,[],[f85,f91])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f61,f60])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f480,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f57,f409])).

fof(f57,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f487,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f486,f51])).

fof(f486,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f485,f53])).

fof(f485,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f484,f54])).

fof(f484,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f481,f56])).

fof(f481,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f89,f409])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

% (4187)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f208,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_relat_1(X3),k1_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X3)
      | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f68,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f534,plain,
    ( ~ spl4_14
    | spl4_15 ),
    inference(avatar_split_clause,[],[f525,f531,f527])).

fof(f525,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),sK0) ),
    inference(forward_demodulation,[],[f524,f94])).

fof(f94,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f65,f60])).

fof(f65,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f524,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f523,f94])).

fof(f523,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f522,f121])).

fof(f522,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f514,f120])).

fof(f514,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0)))
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f220,f509])).

fof(f220,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2)))
      | ~ v1_relat_1(X3)
      | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f69,f80])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f521,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f520])).

fof(f520,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f510,f92])).

fof(f510,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_13 ),
    inference(backward_demodulation,[],[f506,f509])).

fof(f506,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f504])).

fof(f110,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f58,f107,f103])).

fof(f58,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:18:52 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.50  % (4178)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (4176)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (4186)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (4199)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (4192)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (4194)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (4174)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (4185)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (4186)Refutation not found, incomplete strategy% (4186)------------------------------
% 0.21/0.52  % (4186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4186)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4186)Memory used [KB]: 10746
% 0.21/0.52  % (4186)Time elapsed: 0.102 s
% 0.21/0.52  % (4186)------------------------------
% 0.21/0.52  % (4186)------------------------------
% 0.21/0.53  % (4183)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (4190)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (4177)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (4197)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (4175)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (4198)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (4170)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (4189)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (4184)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (4193)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (4188)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (4181)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (4173)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (4182)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (4196)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (4195)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (4179)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.42/0.56  % (4191)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.42/0.56  % (4198)Refutation not found, incomplete strategy% (4198)------------------------------
% 1.42/0.56  % (4198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (4198)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (4198)Memory used [KB]: 10874
% 1.42/0.56  % (4198)Time elapsed: 0.143 s
% 1.42/0.56  % (4198)------------------------------
% 1.42/0.56  % (4198)------------------------------
% 1.42/0.56  % (4171)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.42/0.56  % (4180)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.42/0.57  % (4176)Refutation found. Thanks to Tanya!
% 1.42/0.57  % SZS status Theorem for theBenchmark
% 1.42/0.57  % SZS output start Proof for theBenchmark
% 1.42/0.57  fof(f922,plain,(
% 1.42/0.57    $false),
% 1.42/0.57    inference(avatar_sat_refutation,[],[f110,f521,f534,f547,f656,f689,f701,f790,f872,f921])).
% 1.42/0.57  fof(f921,plain,(
% 1.42/0.57    ~spl4_12 | ~spl4_17 | spl4_32),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f920])).
% 1.42/0.57  fof(f920,plain,(
% 1.42/0.57    $false | (~spl4_12 | ~spl4_17 | spl4_32)),
% 1.42/0.57    inference(subsumption_resolution,[],[f837,f802])).
% 1.42/0.57  fof(f802,plain,(
% 1.42/0.57    k1_xboole_0 != sK2 | spl4_32),
% 1.42/0.57    inference(avatar_component_clause,[],[f801])).
% 1.42/0.57  fof(f801,plain,(
% 1.42/0.57    spl4_32 <=> k1_xboole_0 = sK2),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.42/0.57  fof(f837,plain,(
% 1.42/0.57    k1_xboole_0 = sK2 | (~spl4_12 | ~spl4_17)),
% 1.42/0.57    inference(subsumption_resolution,[],[f836,f120])).
% 1.42/0.57  fof(f120,plain,(
% 1.42/0.57    v1_relat_1(sK2)),
% 1.42/0.57    inference(subsumption_resolution,[],[f118,f71])).
% 1.42/0.57  fof(f71,plain,(
% 1.42/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.42/0.57    inference(cnf_transformation,[],[f5])).
% 1.42/0.57  fof(f5,axiom,(
% 1.42/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.42/0.57  fof(f118,plain,(
% 1.42/0.57    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.42/0.57    inference(resolution,[],[f70,f53])).
% 1.42/0.57  fof(f53,plain,(
% 1.42/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.42/0.57    inference(cnf_transformation,[],[f44])).
% 1.42/0.57  fof(f44,plain,(
% 1.42/0.57    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.42/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f43,f42])).
% 1.42/0.57  fof(f42,plain,(
% 1.42/0.57    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.42/0.57    introduced(choice_axiom,[])).
% 1.42/0.57  fof(f43,plain,(
% 1.42/0.57    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.42/0.57    introduced(choice_axiom,[])).
% 1.42/0.57  fof(f23,plain,(
% 1.42/0.57    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.42/0.57    inference(flattening,[],[f22])).
% 1.42/0.57  fof(f22,plain,(
% 1.42/0.57    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.42/0.57    inference(ennf_transformation,[],[f21])).
% 1.42/0.57  fof(f21,negated_conjecture,(
% 1.42/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.42/0.57    inference(negated_conjecture,[],[f20])).
% 1.42/0.57  fof(f20,conjecture,(
% 1.42/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 1.42/0.57  fof(f70,plain,(
% 1.42/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f28])).
% 1.42/0.57  fof(f28,plain,(
% 1.42/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.42/0.57    inference(ennf_transformation,[],[f2])).
% 1.42/0.57  fof(f2,axiom,(
% 1.42/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.42/0.57  fof(f836,plain,(
% 1.42/0.57    k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | (~spl4_12 | ~spl4_17)),
% 1.42/0.57    inference(trivial_inequality_removal,[],[f822])).
% 1.42/0.57  fof(f822,plain,(
% 1.42/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | (~spl4_12 | ~spl4_17)),
% 1.42/0.57    inference(superposition,[],[f66,f791])).
% 1.42/0.57  fof(f791,plain,(
% 1.42/0.57    k1_xboole_0 = k1_relat_1(sK2) | (~spl4_12 | ~spl4_17)),
% 1.42/0.57    inference(forward_demodulation,[],[f546,f502])).
% 1.42/0.57  fof(f502,plain,(
% 1.42/0.57    k1_xboole_0 = sK0 | ~spl4_12),
% 1.42/0.57    inference(avatar_component_clause,[],[f500])).
% 1.42/0.57  fof(f500,plain,(
% 1.42/0.57    spl4_12 <=> k1_xboole_0 = sK0),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.42/0.57  fof(f546,plain,(
% 1.42/0.57    sK0 = k1_relat_1(sK2) | ~spl4_17),
% 1.42/0.57    inference(avatar_component_clause,[],[f544])).
% 1.42/0.57  fof(f544,plain,(
% 1.42/0.57    spl4_17 <=> sK0 = k1_relat_1(sK2)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.42/0.57  fof(f66,plain,(
% 1.42/0.57    ( ! [X0] : (k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f25])).
% 1.42/0.57  fof(f25,plain,(
% 1.42/0.57    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 1.42/0.57    inference(flattening,[],[f24])).
% 1.42/0.57  fof(f24,plain,(
% 1.42/0.57    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 1.42/0.57    inference(ennf_transformation,[],[f8])).
% 1.42/0.57  fof(f8,axiom,(
% 1.42/0.57    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.42/0.57  fof(f872,plain,(
% 1.42/0.57    spl4_1 | ~spl4_32),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f871])).
% 1.42/0.57  fof(f871,plain,(
% 1.42/0.57    $false | (spl4_1 | ~spl4_32)),
% 1.42/0.57    inference(subsumption_resolution,[],[f859,f112])).
% 1.42/0.57  fof(f112,plain,(
% 1.42/0.57    v2_funct_1(k1_xboole_0)),
% 1.42/0.57    inference(superposition,[],[f92,f90])).
% 1.42/0.57  fof(f90,plain,(
% 1.42/0.57    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.42/0.57    inference(definition_unfolding,[],[f59,f60])).
% 1.42/0.57  fof(f60,plain,(
% 1.42/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f18])).
% 1.42/0.57  fof(f18,axiom,(
% 1.42/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.42/0.57  fof(f59,plain,(
% 1.42/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.42/0.57    inference(cnf_transformation,[],[f10])).
% 1.42/0.57  fof(f10,axiom,(
% 1.42/0.57    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 1.42/0.57  fof(f92,plain,(
% 1.42/0.57    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.42/0.57    inference(definition_unfolding,[],[f63,f60])).
% 1.42/0.57  fof(f63,plain,(
% 1.42/0.57    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.42/0.57    inference(cnf_transformation,[],[f11])).
% 1.42/0.57  fof(f11,axiom,(
% 1.42/0.57    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.42/0.57  fof(f859,plain,(
% 1.42/0.57    ~v2_funct_1(k1_xboole_0) | (spl4_1 | ~spl4_32)),
% 1.42/0.57    inference(backward_demodulation,[],[f105,f803])).
% 1.42/0.57  fof(f803,plain,(
% 1.42/0.57    k1_xboole_0 = sK2 | ~spl4_32),
% 1.42/0.57    inference(avatar_component_clause,[],[f801])).
% 1.42/0.57  fof(f105,plain,(
% 1.42/0.57    ~v2_funct_1(sK2) | spl4_1),
% 1.42/0.57    inference(avatar_component_clause,[],[f103])).
% 1.42/0.57  fof(f103,plain,(
% 1.42/0.57    spl4_1 <=> v2_funct_1(sK2)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.42/0.57  fof(f790,plain,(
% 1.42/0.57    ~spl4_12 | spl4_16),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f789])).
% 1.42/0.57  fof(f789,plain,(
% 1.42/0.57    $false | (~spl4_12 | spl4_16)),
% 1.42/0.57    inference(subsumption_resolution,[],[f788,f120])).
% 1.42/0.57  fof(f788,plain,(
% 1.42/0.57    ~v1_relat_1(sK2) | (~spl4_12 | spl4_16)),
% 1.42/0.57    inference(subsumption_resolution,[],[f787,f565])).
% 1.42/0.57  fof(f565,plain,(
% 1.42/0.57    v4_relat_1(sK2,k1_xboole_0) | ~spl4_12),
% 1.42/0.57    inference(backward_demodulation,[],[f189,f502])).
% 1.42/0.57  fof(f189,plain,(
% 1.42/0.57    v4_relat_1(sK2,sK0)),
% 1.42/0.57    inference(resolution,[],[f81,f53])).
% 1.42/0.57  fof(f81,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f33])).
% 1.42/0.57  fof(f33,plain,(
% 1.42/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.57    inference(ennf_transformation,[],[f12])).
% 1.42/0.57  fof(f12,axiom,(
% 1.42/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.42/0.57  fof(f787,plain,(
% 1.42/0.57    ~v4_relat_1(sK2,k1_xboole_0) | ~v1_relat_1(sK2) | (~spl4_12 | spl4_16)),
% 1.42/0.57    inference(resolution,[],[f773,f72])).
% 1.42/0.57  fof(f72,plain,(
% 1.42/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f45])).
% 1.42/0.57  fof(f45,plain,(
% 1.42/0.57    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.42/0.57    inference(nnf_transformation,[],[f29])).
% 1.42/0.57  fof(f29,plain,(
% 1.42/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.42/0.57    inference(ennf_transformation,[],[f3])).
% 1.42/0.57  fof(f3,axiom,(
% 1.42/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.42/0.57  fof(f773,plain,(
% 1.42/0.57    ~r1_tarski(k1_relat_1(sK2),k1_xboole_0) | (~spl4_12 | spl4_16)),
% 1.42/0.57    inference(forward_demodulation,[],[f542,f502])).
% 1.42/0.57  fof(f542,plain,(
% 1.42/0.57    ~r1_tarski(k1_relat_1(sK2),sK0) | spl4_16),
% 1.42/0.57    inference(avatar_component_clause,[],[f540])).
% 1.42/0.57  fof(f540,plain,(
% 1.42/0.57    spl4_16 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.42/0.57  fof(f701,plain,(
% 1.42/0.57    spl4_12 | ~spl4_13 | spl4_1),
% 1.42/0.57    inference(avatar_split_clause,[],[f498,f103,f504,f500])).
% 1.42/0.57  fof(f504,plain,(
% 1.42/0.57    spl4_13 <=> v2_funct_1(k5_relat_1(sK2,sK3))),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.42/0.57  fof(f498,plain,(
% 1.42/0.57    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | spl4_1),
% 1.42/0.57    inference(subsumption_resolution,[],[f497,f51])).
% 1.42/0.57  fof(f51,plain,(
% 1.42/0.57    v1_funct_1(sK2)),
% 1.42/0.57    inference(cnf_transformation,[],[f44])).
% 1.42/0.57  fof(f497,plain,(
% 1.42/0.57    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK2) | spl4_1),
% 1.42/0.57    inference(subsumption_resolution,[],[f496,f52])).
% 1.42/0.57  fof(f52,plain,(
% 1.42/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.42/0.57    inference(cnf_transformation,[],[f44])).
% 1.42/0.57  fof(f496,plain,(
% 1.42/0.57    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.42/0.57    inference(subsumption_resolution,[],[f495,f53])).
% 1.42/0.57  fof(f495,plain,(
% 1.42/0.57    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.42/0.57    inference(subsumption_resolution,[],[f494,f54])).
% 1.42/0.57  fof(f54,plain,(
% 1.42/0.57    v1_funct_1(sK3)),
% 1.42/0.57    inference(cnf_transformation,[],[f44])).
% 1.42/0.57  fof(f494,plain,(
% 1.42/0.57    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.42/0.57    inference(subsumption_resolution,[],[f493,f55])).
% 1.42/0.57  fof(f55,plain,(
% 1.42/0.57    v1_funct_2(sK3,sK1,sK0)),
% 1.42/0.57    inference(cnf_transformation,[],[f44])).
% 1.42/0.57  fof(f493,plain,(
% 1.42/0.57    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.42/0.57    inference(subsumption_resolution,[],[f492,f56])).
% 1.42/0.57  fof(f56,plain,(
% 1.42/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.42/0.57    inference(cnf_transformation,[],[f44])).
% 1.42/0.57  fof(f492,plain,(
% 1.42/0.57    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | spl4_1),
% 1.42/0.57    inference(subsumption_resolution,[],[f483,f105])).
% 1.42/0.57  fof(f483,plain,(
% 1.42/0.57    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.42/0.57    inference(superposition,[],[f83,f409])).
% 1.42/0.57  fof(f409,plain,(
% 1.42/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.42/0.57    inference(subsumption_resolution,[],[f405,f51])).
% 1.42/0.57  fof(f405,plain,(
% 1.42/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 1.42/0.57    inference(resolution,[],[f269,f53])).
% 1.42/0.57  fof(f269,plain,(
% 1.42/0.57    ( ! [X12,X10,X11] : (~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | k1_partfun1(X10,X11,sK1,sK0,X12,sK3) = k5_relat_1(X12,sK3) | ~v1_funct_1(X12)) )),
% 1.42/0.57    inference(subsumption_resolution,[],[f259,f54])).
% 1.42/0.57  fof(f259,plain,(
% 1.42/0.57    ( ! [X12,X10,X11] : (k1_partfun1(X10,X11,sK1,sK0,X12,sK3) = k5_relat_1(X12,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~v1_funct_1(X12)) )),
% 1.42/0.57    inference(resolution,[],[f87,f56])).
% 1.42/0.57  fof(f87,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f39])).
% 1.42/0.57  fof(f39,plain,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.42/0.57    inference(flattening,[],[f38])).
% 1.42/0.57  fof(f38,plain,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.42/0.57    inference(ennf_transformation,[],[f17])).
% 1.42/0.57  fof(f17,axiom,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.42/0.57  fof(f83,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f35])).
% 1.42/0.57  fof(f35,plain,(
% 1.42/0.57    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.42/0.57    inference(flattening,[],[f34])).
% 1.42/0.57  fof(f34,plain,(
% 1.42/0.57    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.42/0.57    inference(ennf_transformation,[],[f19])).
% 1.42/0.57  fof(f19,axiom,(
% 1.42/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 1.42/0.57  fof(f689,plain,(
% 1.42/0.57    spl4_2 | ~spl4_15),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f688])).
% 1.42/0.57  fof(f688,plain,(
% 1.42/0.57    $false | (spl4_2 | ~spl4_15)),
% 1.42/0.57    inference(subsumption_resolution,[],[f687,f121])).
% 1.42/0.57  fof(f121,plain,(
% 1.42/0.57    v1_relat_1(sK3)),
% 1.42/0.57    inference(subsumption_resolution,[],[f119,f71])).
% 1.42/0.57  fof(f119,plain,(
% 1.42/0.57    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.42/0.57    inference(resolution,[],[f70,f56])).
% 1.42/0.57  fof(f687,plain,(
% 1.42/0.57    ~v1_relat_1(sK3) | (spl4_2 | ~spl4_15)),
% 1.42/0.57    inference(subsumption_resolution,[],[f679,f109])).
% 1.42/0.57  fof(f109,plain,(
% 1.42/0.57    ~v2_funct_2(sK3,sK0) | spl4_2),
% 1.42/0.57    inference(avatar_component_clause,[],[f107])).
% 1.42/0.57  fof(f107,plain,(
% 1.42/0.57    spl4_2 <=> v2_funct_2(sK3,sK0)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.42/0.57  fof(f679,plain,(
% 1.42/0.57    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_15),
% 1.42/0.57    inference(superposition,[],[f202,f533])).
% 1.42/0.57  fof(f533,plain,(
% 1.42/0.57    sK0 = k2_relat_1(sK3) | ~spl4_15),
% 1.42/0.57    inference(avatar_component_clause,[],[f531])).
% 1.42/0.57  fof(f531,plain,(
% 1.42/0.57    spl4_15 <=> sK0 = k2_relat_1(sK3)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.42/0.57  fof(f202,plain,(
% 1.42/0.57    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.42/0.57    inference(subsumption_resolution,[],[f96,f155])).
% 1.42/0.57  fof(f155,plain,(
% 1.42/0.57    ( ! [X2] : (v5_relat_1(X2,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.42/0.57    inference(resolution,[],[f75,f97])).
% 1.42/0.57  fof(f97,plain,(
% 1.42/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.42/0.57    inference(equality_resolution,[],[f79])).
% 1.42/0.57  fof(f79,plain,(
% 1.42/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.42/0.57    inference(cnf_transformation,[],[f49])).
% 1.42/0.57  fof(f49,plain,(
% 1.42/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.57    inference(flattening,[],[f48])).
% 1.42/0.57  fof(f48,plain,(
% 1.42/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.57    inference(nnf_transformation,[],[f1])).
% 1.42/0.57  fof(f1,axiom,(
% 1.42/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.42/0.57  fof(f75,plain,(
% 1.42/0.57    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f46])).
% 1.42/0.57  fof(f46,plain,(
% 1.42/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.42/0.57    inference(nnf_transformation,[],[f30])).
% 1.42/0.57  fof(f30,plain,(
% 1.42/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.42/0.57    inference(ennf_transformation,[],[f4])).
% 1.42/0.57  fof(f4,axiom,(
% 1.42/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.42/0.57  fof(f96,plain,(
% 1.42/0.57    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.42/0.57    inference(equality_resolution,[],[f77])).
% 1.42/0.57  fof(f77,plain,(
% 1.42/0.57    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f47])).
% 1.42/0.57  fof(f47,plain,(
% 1.42/0.57    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.42/0.57    inference(nnf_transformation,[],[f32])).
% 1.42/0.57  fof(f32,plain,(
% 1.42/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.42/0.57    inference(flattening,[],[f31])).
% 1.42/0.57  fof(f31,plain,(
% 1.42/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.42/0.57    inference(ennf_transformation,[],[f15])).
% 1.42/0.57  fof(f15,axiom,(
% 1.42/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.42/0.57  fof(f656,plain,(
% 1.42/0.57    spl4_14),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f655])).
% 1.42/0.57  fof(f655,plain,(
% 1.42/0.57    $false | spl4_14),
% 1.42/0.57    inference(subsumption_resolution,[],[f654,f121])).
% 1.42/0.57  fof(f654,plain,(
% 1.42/0.57    ~v1_relat_1(sK3) | spl4_14),
% 1.42/0.57    inference(subsumption_resolution,[],[f653,f199])).
% 1.42/0.57  fof(f199,plain,(
% 1.42/0.57    v5_relat_1(sK3,sK0)),
% 1.42/0.57    inference(resolution,[],[f82,f56])).
% 1.42/0.57  fof(f82,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f33])).
% 1.42/0.57  fof(f653,plain,(
% 1.42/0.57    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | spl4_14),
% 1.42/0.57    inference(resolution,[],[f529,f74])).
% 1.42/0.57  fof(f74,plain,(
% 1.42/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f46])).
% 1.42/0.57  fof(f529,plain,(
% 1.42/0.57    ~r1_tarski(k2_relat_1(sK3),sK0) | spl4_14),
% 1.42/0.57    inference(avatar_component_clause,[],[f527])).
% 1.42/0.57  fof(f527,plain,(
% 1.42/0.57    spl4_14 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.42/0.57  fof(f547,plain,(
% 1.42/0.57    ~spl4_16 | spl4_17),
% 1.42/0.57    inference(avatar_split_clause,[],[f538,f544,f540])).
% 1.42/0.57  fof(f538,plain,(
% 1.42/0.57    sK0 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK0)),
% 1.42/0.57    inference(forward_demodulation,[],[f537,f95])).
% 1.42/0.57  fof(f95,plain,(
% 1.42/0.57    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.42/0.57    inference(definition_unfolding,[],[f64,f60])).
% 1.42/0.57  fof(f64,plain,(
% 1.42/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.42/0.57    inference(cnf_transformation,[],[f9])).
% 1.42/0.57  fof(f9,axiom,(
% 1.42/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.42/0.57  fof(f537,plain,(
% 1.42/0.57    ~r1_tarski(k1_relat_1(sK2),sK0) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))),
% 1.42/0.57    inference(forward_demodulation,[],[f536,f95])).
% 1.42/0.57  fof(f536,plain,(
% 1.42/0.57    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0))),
% 1.42/0.57    inference(subsumption_resolution,[],[f535,f121])).
% 1.42/0.57  fof(f535,plain,(
% 1.42/0.57    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.42/0.57    inference(subsumption_resolution,[],[f515,f120])).
% 1.42/0.57  fof(f515,plain,(
% 1.42/0.57    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k6_partfun1(sK0))) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k1_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.42/0.57    inference(superposition,[],[f208,f509])).
% 1.42/0.57  fof(f509,plain,(
% 1.42/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.42/0.57    inference(global_subsumption,[],[f487,f508])).
% 1.42/0.57  fof(f508,plain,(
% 1.42/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.42/0.57    inference(resolution,[],[f480,f247])).
% 1.42/0.57  fof(f247,plain,(
% 1.42/0.57    ( ! [X2,X1] : (~r2_relset_1(X1,X1,X2,k6_partfun1(X1)) | k6_partfun1(X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))) )),
% 1.42/0.57    inference(resolution,[],[f85,f91])).
% 1.42/0.57  fof(f91,plain,(
% 1.42/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.42/0.57    inference(definition_unfolding,[],[f61,f60])).
% 1.42/0.57  fof(f61,plain,(
% 1.42/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.42/0.57    inference(cnf_transformation,[],[f14])).
% 1.42/0.57  fof(f14,axiom,(
% 1.42/0.57    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.42/0.57  fof(f85,plain,(
% 1.42/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.42/0.57    inference(cnf_transformation,[],[f50])).
% 1.42/0.57  fof(f50,plain,(
% 1.42/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.57    inference(nnf_transformation,[],[f37])).
% 1.42/0.57  fof(f37,plain,(
% 1.42/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.57    inference(flattening,[],[f36])).
% 1.42/0.57  fof(f36,plain,(
% 1.42/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.42/0.57    inference(ennf_transformation,[],[f13])).
% 1.42/0.57  fof(f13,axiom,(
% 1.42/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.42/0.57  fof(f480,plain,(
% 1.42/0.57    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.42/0.57    inference(backward_demodulation,[],[f57,f409])).
% 1.42/0.57  fof(f57,plain,(
% 1.42/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.42/0.57    inference(cnf_transformation,[],[f44])).
% 1.42/0.57  fof(f487,plain,(
% 1.42/0.57    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.42/0.57    inference(subsumption_resolution,[],[f486,f51])).
% 1.42/0.57  fof(f486,plain,(
% 1.42/0.57    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.42/0.57    inference(subsumption_resolution,[],[f485,f53])).
% 1.42/0.57  fof(f485,plain,(
% 1.42/0.57    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.42/0.57    inference(subsumption_resolution,[],[f484,f54])).
% 1.42/0.57  fof(f484,plain,(
% 1.42/0.57    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.42/0.57    inference(subsumption_resolution,[],[f481,f56])).
% 1.42/0.57  fof(f481,plain,(
% 1.42/0.57    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.42/0.57    inference(superposition,[],[f89,f409])).
% 1.42/0.57  fof(f89,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f41])).
% 1.42/0.57  fof(f41,plain,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.42/0.57    inference(flattening,[],[f40])).
% 1.42/0.57  fof(f40,plain,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.42/0.57    inference(ennf_transformation,[],[f16])).
% 1.42/0.57  fof(f16,axiom,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.42/0.57  % (4187)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.42/0.57  fof(f208,plain,(
% 1.42/0.57    ( ! [X2,X3] : (~r1_tarski(k1_relat_1(X3),k1_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X3) | k1_relat_1(X3) = k1_relat_1(k5_relat_1(X3,X2)) | ~v1_relat_1(X2)) )),
% 1.42/0.57    inference(resolution,[],[f68,f80])).
% 1.42/0.57  fof(f80,plain,(
% 1.42/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f49])).
% 1.42/0.57  fof(f68,plain,(
% 1.42/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f26])).
% 1.42/0.57  fof(f26,plain,(
% 1.42/0.57    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.42/0.57    inference(ennf_transformation,[],[f6])).
% 1.42/0.57  fof(f6,axiom,(
% 1.42/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 1.42/0.57  fof(f534,plain,(
% 1.42/0.57    ~spl4_14 | spl4_15),
% 1.42/0.57    inference(avatar_split_clause,[],[f525,f531,f527])).
% 1.42/0.57  fof(f525,plain,(
% 1.42/0.57    sK0 = k2_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),sK0)),
% 1.42/0.57    inference(forward_demodulation,[],[f524,f94])).
% 1.42/0.57  fof(f94,plain,(
% 1.42/0.57    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.42/0.57    inference(definition_unfolding,[],[f65,f60])).
% 1.42/0.57  fof(f65,plain,(
% 1.42/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.42/0.57    inference(cnf_transformation,[],[f9])).
% 1.42/0.57  fof(f524,plain,(
% 1.42/0.57    ~r1_tarski(k2_relat_1(sK3),sK0) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))),
% 1.42/0.57    inference(forward_demodulation,[],[f523,f94])).
% 1.42/0.57  fof(f523,plain,(
% 1.42/0.57    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0))),
% 1.42/0.57    inference(subsumption_resolution,[],[f522,f121])).
% 1.42/0.57  fof(f522,plain,(
% 1.42/0.57    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.42/0.57    inference(subsumption_resolution,[],[f514,f120])).
% 1.42/0.57  fof(f514,plain,(
% 1.42/0.57    ~r1_tarski(k2_relat_1(sK3),k2_relat_1(k6_partfun1(sK0))) | ~v1_relat_1(sK2) | k2_relat_1(sK3) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK3)),
% 1.42/0.57    inference(superposition,[],[f220,f509])).
% 1.42/0.57  fof(f220,plain,(
% 1.42/0.57    ( ! [X2,X3] : (~r1_tarski(k2_relat_1(X2),k2_relat_1(k5_relat_1(X3,X2))) | ~v1_relat_1(X3) | k2_relat_1(X2) = k2_relat_1(k5_relat_1(X3,X2)) | ~v1_relat_1(X2)) )),
% 1.42/0.57    inference(resolution,[],[f69,f80])).
% 1.42/0.57  fof(f69,plain,(
% 1.42/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f27])).
% 1.42/0.57  fof(f27,plain,(
% 1.42/0.57    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.42/0.57    inference(ennf_transformation,[],[f7])).
% 1.42/0.57  fof(f7,axiom,(
% 1.42/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.42/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.42/0.57  fof(f521,plain,(
% 1.42/0.57    spl4_13),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f520])).
% 1.42/0.57  fof(f520,plain,(
% 1.42/0.57    $false | spl4_13),
% 1.42/0.57    inference(subsumption_resolution,[],[f510,f92])).
% 1.42/0.57  fof(f510,plain,(
% 1.42/0.57    ~v2_funct_1(k6_partfun1(sK0)) | spl4_13),
% 1.42/0.57    inference(backward_demodulation,[],[f506,f509])).
% 1.42/0.57  fof(f506,plain,(
% 1.42/0.57    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_13),
% 1.42/0.57    inference(avatar_component_clause,[],[f504])).
% 1.42/0.57  fof(f110,plain,(
% 1.42/0.57    ~spl4_1 | ~spl4_2),
% 1.42/0.57    inference(avatar_split_clause,[],[f58,f107,f103])).
% 1.42/0.57  fof(f58,plain,(
% 1.42/0.57    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.42/0.57    inference(cnf_transformation,[],[f44])).
% 1.42/0.57  % SZS output end Proof for theBenchmark
% 1.42/0.57  % (4176)------------------------------
% 1.42/0.57  % (4176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (4176)Termination reason: Refutation
% 1.42/0.57  
% 1.42/0.57  % (4176)Memory used [KB]: 11257
% 1.42/0.57  % (4176)Time elapsed: 0.147 s
% 1.42/0.57  % (4176)------------------------------
% 1.42/0.57  % (4176)------------------------------
% 1.42/0.57  % (4180)Refutation not found, incomplete strategy% (4180)------------------------------
% 1.42/0.57  % (4180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (4180)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.57  
% 1.42/0.57  % (4180)Memory used [KB]: 10874
% 1.42/0.57  % (4180)Time elapsed: 0.151 s
% 1.42/0.57  % (4180)------------------------------
% 1.42/0.57  % (4180)------------------------------
% 1.62/0.57  % (4172)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.62/0.58  % (4169)Success in time 0.207 s
%------------------------------------------------------------------------------
