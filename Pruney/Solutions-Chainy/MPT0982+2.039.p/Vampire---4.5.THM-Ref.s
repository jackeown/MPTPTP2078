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
% DateTime   : Thu Dec  3 13:01:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 319 expanded)
%              Number of leaves         :   23 ( 101 expanded)
%              Depth                    :   15
%              Number of atoms          :  427 (2332 expanded)
%              Number of equality atoms :  119 ( 723 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f696,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f159,f183,f319,f394,f475,f663,f695])).

fof(f695,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | ~ spl5_11
    | ~ spl5_25 ),
    inference(avatar_contradiction_clause,[],[f694])).

fof(f694,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_11
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f693,f418])).

fof(f418,plain,(
    r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(resolution,[],[f417,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f417,plain,(
    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f416,f44])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK3)
    & k1_xboole_0 != sK2
    & v2_funct_1(sK4)
    & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f39,f38])).

fof(f38,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( sK1 != k2_relset_1(sK0,sK1,sK3)
          & k1_xboole_0 != sK2
          & v2_funct_1(X4)
          & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X4] :
        ( sK1 != k2_relset_1(sK0,sK1,sK3)
        & k1_xboole_0 != sK2
        & v2_funct_1(X4)
        & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X4,sK1,sK2)
        & v1_funct_1(X4) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK3)
      & k1_xboole_0 != sK2
      & v2_funct_1(sK4)
      & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

fof(f416,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f67,f144])).

fof(f144,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f44,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f693,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_11
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f692,f399])).

fof(f399,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f395,f47])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f395,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_11 ),
    inference(superposition,[],[f135,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f135,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_11
  <=> sK1 = k1_relset_1(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f692,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_11
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f691,f198])).

fof(f198,plain,(
    sK1 != k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f197,f44])).

fof(f197,plain,
    ( sK1 != k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f51,f62])).

fof(f51,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f691,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_11
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f690,f485])).

fof(f485,plain,
    ( sK1 = k10_relat_1(sK4,sK2)
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f484,f135])).

fof(f484,plain,(
    k1_relset_1(sK1,sK2,sK4) = k10_relat_1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f482,f47])).

fof(f482,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k10_relat_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(superposition,[],[f167,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f167,plain,(
    ! [X12] : k8_relset_1(sK1,sK2,sK4,X12) = k10_relat_1(sK4,X12) ),
    inference(resolution,[],[f47,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f690,plain,
    ( k2_relat_1(sK3) = k10_relat_1(sK4,sK2)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f689,f97])).

fof(f97,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_4
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f689,plain,
    ( k2_relat_1(sK3) = k10_relat_1(sK4,sK2)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f688,f45])).

fof(f45,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f688,plain,
    ( k2_relat_1(sK3) = k10_relat_1(sK4,sK2)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_25 ),
    inference(subsumption_resolution,[],[f684,f49])).

fof(f49,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f684,plain,
    ( k2_relat_1(sK3) = k10_relat_1(sK4,sK2)
    | ~ v2_funct_1(sK4)
    | ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_25 ),
    inference(superposition,[],[f58,f676])).

fof(f676,plain,
    ( sK2 = k9_relat_1(sK4,k2_relat_1(sK3))
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_25 ),
    inference(backward_demodulation,[],[f527,f472])).

fof(f472,plain,
    ( sK2 = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f470])).

fof(f470,plain,
    ( spl5_25
  <=> sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f527,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3))
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(resolution,[],[f186,f97])).

fof(f186,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k5_relat_1(sK3,X1)) = k9_relat_1(X1,k2_relat_1(sK3)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f82,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f82,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl5_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f663,plain,(
    spl5_24 ),
    inference(avatar_contradiction_clause,[],[f662])).

fof(f662,plain,
    ( $false
    | spl5_24 ),
    inference(subsumption_resolution,[],[f661,f44])).

fof(f661,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_24 ),
    inference(subsumption_resolution,[],[f660,f47])).

fof(f660,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_24 ),
    inference(subsumption_resolution,[],[f659,f468])).

fof(f468,plain,
    ( ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f466])).

fof(f466,plain,
    ( spl5_24
  <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f659,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f71,f515])).

fof(f515,plain,(
    k5_relat_1(sK3,sK4) = k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) ),
    inference(resolution,[],[f139,f47])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k4_relset_1(sK0,sK1,X0,X1,sK3,X2) = k5_relat_1(sK3,X2) ) ),
    inference(resolution,[],[f44,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f475,plain,
    ( ~ spl5_24
    | spl5_25 ),
    inference(avatar_split_clause,[],[f464,f470,f466])).

fof(f464,plain,
    ( sK2 = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(superposition,[],[f62,f376])).

fof(f376,plain,(
    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f375,f42])).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f375,plain,
    ( sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f374,f44])).

fof(f374,plain,
    ( sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f373,f45])).

fof(f373,plain,
    ( sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f369,f47])).

fof(f369,plain,
    ( sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f48,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f48,plain,(
    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f394,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | spl5_10 ),
    inference(subsumption_resolution,[],[f131,f47])).

fof(f131,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_10
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f319,plain,
    ( ~ spl5_10
    | spl5_11 ),
    inference(avatar_split_clause,[],[f318,f133,f129])).

fof(f318,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f317,f50])).

fof(f50,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f40])).

fof(f317,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f46,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f46,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f183,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl5_4 ),
    inference(subsumption_resolution,[],[f181,f69])).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f181,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | spl5_4 ),
    inference(subsumption_resolution,[],[f176,f98])).

fof(f98,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f176,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f47,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f159,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f157,f69])).

fof(f157,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f152,f83])).

fof(f83,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f81])).

fof(f152,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f44,f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:51:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (21983)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.45  % (21983)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f696,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f159,f183,f319,f394,f475,f663,f695])).
% 0.21/0.45  fof(f695,plain,(
% 0.21/0.45    ~spl5_1 | ~spl5_4 | ~spl5_11 | ~spl5_25),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f694])).
% 0.21/0.45  fof(f694,plain,(
% 0.21/0.45    $false | (~spl5_1 | ~spl5_4 | ~spl5_11 | ~spl5_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f693,f418])).
% 0.21/0.45  fof(f418,plain,(
% 0.21/0.45    r1_tarski(k2_relat_1(sK3),sK1)),
% 0.21/0.45    inference(resolution,[],[f417,f70])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.45    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.45  fof(f417,plain,(
% 0.21/0.45    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.21/0.45    inference(subsumption_resolution,[],[f416,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.45    inference(cnf_transformation,[],[f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(sK4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f39,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(X4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    ? [X4] : (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(X4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) => (sK1 != k2_relset_1(sK0,sK1,sK3) & k1_xboole_0 != sK2 & v2_funct_1(sK4) & sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.45    inference(flattening,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.45    inference(ennf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.21/0.45    inference(negated_conjecture,[],[f15])).
% 0.21/0.45  fof(f15,conjecture,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).
% 0.21/0.45  fof(f416,plain,(
% 0.21/0.45    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.45    inference(superposition,[],[f67,f144])).
% 0.21/0.45  fof(f144,plain,(
% 0.21/0.45    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.21/0.45    inference(resolution,[],[f44,f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.45  fof(f693,plain,(
% 0.21/0.45    ~r1_tarski(k2_relat_1(sK3),sK1) | (~spl5_1 | ~spl5_4 | ~spl5_11 | ~spl5_25)),
% 0.21/0.45    inference(forward_demodulation,[],[f692,f399])).
% 0.21/0.45  fof(f399,plain,(
% 0.21/0.45    sK1 = k1_relat_1(sK4) | ~spl5_11),
% 0.21/0.45    inference(subsumption_resolution,[],[f395,f47])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.45    inference(cnf_transformation,[],[f40])).
% 0.21/0.45  fof(f395,plain,(
% 0.21/0.45    sK1 = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_11),
% 0.21/0.45    inference(superposition,[],[f135,f63])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.45  fof(f135,plain,(
% 0.21/0.45    sK1 = k1_relset_1(sK1,sK2,sK4) | ~spl5_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f133])).
% 0.21/0.45  fof(f133,plain,(
% 0.21/0.45    spl5_11 <=> sK1 = k1_relset_1(sK1,sK2,sK4)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.45  fof(f692,plain,(
% 0.21/0.45    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | (~spl5_1 | ~spl5_4 | ~spl5_11 | ~spl5_25)),
% 0.21/0.45    inference(subsumption_resolution,[],[f691,f198])).
% 0.21/0.45  fof(f198,plain,(
% 0.21/0.45    sK1 != k2_relat_1(sK3)),
% 0.21/0.45    inference(subsumption_resolution,[],[f197,f44])).
% 0.21/0.45  fof(f197,plain,(
% 0.21/0.45    sK1 != k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.45    inference(superposition,[],[f51,f62])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    sK1 != k2_relset_1(sK0,sK1,sK3)),
% 0.21/0.45    inference(cnf_transformation,[],[f40])).
% 0.21/0.45  fof(f691,plain,(
% 0.21/0.45    sK1 = k2_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | (~spl5_1 | ~spl5_4 | ~spl5_11 | ~spl5_25)),
% 0.21/0.45    inference(forward_demodulation,[],[f690,f485])).
% 0.21/0.45  fof(f485,plain,(
% 0.21/0.45    sK1 = k10_relat_1(sK4,sK2) | ~spl5_11),
% 0.21/0.45    inference(forward_demodulation,[],[f484,f135])).
% 0.21/0.45  fof(f484,plain,(
% 0.21/0.45    k1_relset_1(sK1,sK2,sK4) = k10_relat_1(sK4,sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f482,f47])).
% 0.21/0.45  fof(f482,plain,(
% 0.21/0.45    k1_relset_1(sK1,sK2,sK4) = k10_relat_1(sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.45    inference(superposition,[],[f167,f66])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.46  fof(f167,plain,(
% 0.21/0.46    ( ! [X12] : (k8_relset_1(sK1,sK2,sK4,X12) = k10_relat_1(sK4,X12)) )),
% 0.21/0.46    inference(resolution,[],[f47,f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.46  fof(f690,plain,(
% 0.21/0.46    k2_relat_1(sK3) = k10_relat_1(sK4,sK2) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | (~spl5_1 | ~spl5_4 | ~spl5_25)),
% 0.21/0.46    inference(subsumption_resolution,[],[f689,f97])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    v1_relat_1(sK4) | ~spl5_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f96])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    spl5_4 <=> v1_relat_1(sK4)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.46  fof(f689,plain,(
% 0.21/0.46    k2_relat_1(sK3) = k10_relat_1(sK4,sK2) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | (~spl5_1 | ~spl5_4 | ~spl5_25)),
% 0.21/0.46    inference(subsumption_resolution,[],[f688,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    v1_funct_1(sK4)),
% 0.21/0.46    inference(cnf_transformation,[],[f40])).
% 0.21/0.46  fof(f688,plain,(
% 0.21/0.46    k2_relat_1(sK3) = k10_relat_1(sK4,sK2) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | (~spl5_1 | ~spl5_4 | ~spl5_25)),
% 0.21/0.46    inference(subsumption_resolution,[],[f684,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    v2_funct_1(sK4)),
% 0.21/0.46    inference(cnf_transformation,[],[f40])).
% 0.21/0.46  fof(f684,plain,(
% 0.21/0.46    k2_relat_1(sK3) = k10_relat_1(sK4,sK2) | ~v2_funct_1(sK4) | ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | (~spl5_1 | ~spl5_4 | ~spl5_25)),
% 0.21/0.46    inference(superposition,[],[f58,f676])).
% 0.21/0.46  fof(f676,plain,(
% 0.21/0.46    sK2 = k9_relat_1(sK4,k2_relat_1(sK3)) | (~spl5_1 | ~spl5_4 | ~spl5_25)),
% 0.21/0.46    inference(backward_demodulation,[],[f527,f472])).
% 0.21/0.46  fof(f472,plain,(
% 0.21/0.46    sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) | ~spl5_25),
% 0.21/0.46    inference(avatar_component_clause,[],[f470])).
% 0.21/0.46  fof(f470,plain,(
% 0.21/0.46    spl5_25 <=> sK2 = k2_relat_1(k5_relat_1(sK3,sK4))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.46  fof(f527,plain,(
% 0.21/0.46    k2_relat_1(k5_relat_1(sK3,sK4)) = k9_relat_1(sK4,k2_relat_1(sK3)) | (~spl5_1 | ~spl5_4)),
% 0.21/0.46    inference(resolution,[],[f186,f97])).
% 0.21/0.46  fof(f186,plain,(
% 0.21/0.46    ( ! [X1] : (~v1_relat_1(X1) | k2_relat_1(k5_relat_1(sK3,X1)) = k9_relat_1(X1,k2_relat_1(sK3))) ) | ~spl5_1),
% 0.21/0.46    inference(resolution,[],[f82,f64])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    v1_relat_1(sK3) | ~spl5_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f81])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    spl5_1 <=> v1_relat_1(sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.46  fof(f663,plain,(
% 0.21/0.46    spl5_24),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f662])).
% 0.21/0.46  fof(f662,plain,(
% 0.21/0.46    $false | spl5_24),
% 0.21/0.46    inference(subsumption_resolution,[],[f661,f44])).
% 0.21/0.46  fof(f661,plain,(
% 0.21/0.46    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_24),
% 0.21/0.46    inference(subsumption_resolution,[],[f660,f47])).
% 0.21/0.46  fof(f660,plain,(
% 0.21/0.46    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_24),
% 0.21/0.46    inference(subsumption_resolution,[],[f659,f468])).
% 0.21/0.46  fof(f468,plain,(
% 0.21/0.46    ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_24),
% 0.21/0.46    inference(avatar_component_clause,[],[f466])).
% 0.21/0.46  fof(f466,plain,(
% 0.21/0.46    spl5_24 <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.46  fof(f659,plain,(
% 0.21/0.46    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.46    inference(superposition,[],[f71,f515])).
% 0.21/0.46  fof(f515,plain,(
% 0.21/0.46    k5_relat_1(sK3,sK4) = k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4)),
% 0.21/0.46    inference(resolution,[],[f139,f47])).
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k4_relset_1(sK0,sK1,X0,X1,sK3,X2) = k5_relat_1(sK3,X2)) )),
% 0.21/0.46    inference(resolution,[],[f44,f59])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(flattening,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(flattening,[],[f36])).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.46    inference(ennf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 0.21/0.46  fof(f475,plain,(
% 0.21/0.46    ~spl5_24 | spl5_25),
% 0.21/0.46    inference(avatar_split_clause,[],[f464,f470,f466])).
% 0.21/0.46  fof(f464,plain,(
% 0.21/0.46    sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.46    inference(superposition,[],[f62,f376])).
% 0.21/0.46  fof(f376,plain,(
% 0.21/0.46    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4))),
% 0.21/0.46    inference(subsumption_resolution,[],[f375,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    v1_funct_1(sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f40])).
% 0.21/0.46  fof(f375,plain,(
% 0.21/0.46    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f374,f44])).
% 0.21/0.46  fof(f374,plain,(
% 0.21/0.46    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f373,f45])).
% 0.21/0.46  fof(f373,plain,(
% 0.21/0.46    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(subsumption_resolution,[],[f369,f47])).
% 0.21/0.46  fof(f369,plain,(
% 0.21/0.46    sK2 = k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 0.21/0.46    inference(superposition,[],[f48,f60])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.46    inference(flattening,[],[f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.46    inference(ennf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.21/0.46    inference(cnf_transformation,[],[f40])).
% 0.21/0.46  fof(f394,plain,(
% 0.21/0.46    spl5_10),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f393])).
% 0.21/0.46  fof(f393,plain,(
% 0.21/0.46    $false | spl5_10),
% 0.21/0.46    inference(subsumption_resolution,[],[f131,f47])).
% 0.21/0.46  fof(f131,plain,(
% 0.21/0.46    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f129])).
% 0.21/0.46  fof(f129,plain,(
% 0.21/0.46    spl5_10 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.46  fof(f319,plain,(
% 0.21/0.46    ~spl5_10 | spl5_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f318,f133,f129])).
% 0.21/0.46  fof(f318,plain,(
% 0.21/0.46    sK1 = k1_relset_1(sK1,sK2,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.46    inference(subsumption_resolution,[],[f317,f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    k1_xboole_0 != sK2),
% 0.21/0.46    inference(cnf_transformation,[],[f40])).
% 0.21/0.46  fof(f317,plain,(
% 0.21/0.46    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.46    inference(resolution,[],[f46,f52])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(nnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(flattening,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    v1_funct_2(sK4,sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f40])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    spl5_4),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f182])).
% 0.21/0.46  fof(f182,plain,(
% 0.21/0.46    $false | spl5_4),
% 0.21/0.46    inference(subsumption_resolution,[],[f181,f69])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.46  fof(f181,plain,(
% 0.21/0.46    ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | spl5_4),
% 0.21/0.46    inference(subsumption_resolution,[],[f176,f98])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    ~v1_relat_1(sK4) | spl5_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f96])).
% 0.21/0.46  fof(f176,plain,(
% 0.21/0.46    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 0.21/0.46    inference(resolution,[],[f47,f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.46  fof(f159,plain,(
% 0.21/0.46    spl5_1),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f158])).
% 0.21/0.46  fof(f158,plain,(
% 0.21/0.46    $false | spl5_1),
% 0.21/0.46    inference(subsumption_resolution,[],[f157,f69])).
% 0.21/0.46  fof(f157,plain,(
% 0.21/0.46    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl5_1),
% 0.21/0.46    inference(subsumption_resolution,[],[f152,f83])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    ~v1_relat_1(sK3) | spl5_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f81])).
% 0.21/0.46  fof(f152,plain,(
% 0.21/0.46    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.46    inference(resolution,[],[f44,f68])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (21983)------------------------------
% 0.21/0.46  % (21983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (21983)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (21983)Memory used [KB]: 6524
% 0.21/0.46  % (21983)Time elapsed: 0.045 s
% 0.21/0.46  % (21983)------------------------------
% 0.21/0.46  % (21983)------------------------------
% 0.21/0.46  % (21963)Success in time 0.098 s
%------------------------------------------------------------------------------
