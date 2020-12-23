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
% DateTime   : Thu Dec  3 13:01:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 (1045 expanded)
%              Number of leaves         :   16 ( 317 expanded)
%              Depth                    :   26
%              Number of atoms          :  395 (7353 expanded)
%              Number of equality atoms :  157 (1591 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f622,plain,(
    $false ),
    inference(resolution,[],[f607,f180])).

fof(f180,plain,(
    ! [X0,X1] : r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f127,f63])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(subsumption_resolution,[],[f95,f121])).

fof(f121,plain,(
    ! [X0,X1] : ~ sP7(X0,X1) ),
    inference(resolution,[],[f96,f63])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP7(X1,X0) ) ),
    inference(general_splitting,[],[f87,f95_D])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP7(X1,X0) ) ),
    inference(cnf_transformation,[],[f95_D])).

fof(f95_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X1,X2,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    <=> ~ sP7(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f607,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f559,f594])).

fof(f594,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f581,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f72,f62])).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f581,plain,(
    v1_xboole_0(sK4) ),
    inference(resolution,[],[f531,f129])).

fof(f129,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f128,f88])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f67,f62])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f531,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f520,f88])).

fof(f520,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f59,f516])).

fof(f516,plain,(
    k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f181,f484])).

fof(f484,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f61,f480])).

fof(f480,plain,
    ( sK3 = sK4
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f57,f103,f338,f479])).

fof(f479,plain,
    ( k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4))
    | sK3 = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f478])).

fof(f478,plain,
    ( sK1 != sK1
    | k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4))
    | sK3 = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f477])).

fof(f477,plain,
    ( sK1 != sK1
    | k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4))
    | sK3 = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f472,f261])).

fof(f261,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f58,f260])).

fof(f260,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f255,f211])).

fof(f211,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f77,f59])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f255,plain,
    ( ~ v1_funct_2(sK4,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f79,f151])).

fof(f151,plain,(
    sP0(sK1,sK4,sK2) ),
    inference(resolution,[],[f83,f59])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f33,f38])).

fof(f38,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f58,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
    & ! [X4] :
        ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
        | ~ r2_hidden(X4,sK1) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK1,sK2,sK3,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK3,X4)
              | ~ r2_hidden(X4,sK1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK1,sK2,sK3,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK3,X4)
            | ~ r2_hidden(X4,sK1) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
      & ! [X4] :
          ( k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)
          | ~ r2_hidden(X4,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(f472,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | k1_funct_1(sK3,sK5(sK3,X0)) != k1_funct_1(X0,sK5(sK3,X0))
      | sK3 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK2 ) ),
    inference(global_subsumption,[],[f54,f102,f466])).

fof(f466,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | k1_funct_1(sK3,sK5(sK3,X0)) != k1_funct_1(X0,sK5(sK3,X0))
      | sK3 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f65,f259])).

fof(f259,plain,
    ( sK1 = k1_relat_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f55,f258])).

fof(f258,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f254,f210])).

fof(f210,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f77,f56])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f254,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f79,f150])).

fof(f150,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f83,f56])).

fof(f55,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
            & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f102,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f76,f56])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f338,plain,
    ( k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4))
    | k1_xboole_0 = sK2
    | sK3 = sK4 ),
    inference(global_subsumption,[],[f57,f103,f337])).

fof(f337,plain,
    ( sK3 = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_xboole_0 = sK2
    | k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4)) ),
    inference(trivial_inequality_removal,[],[f336])).

fof(f336,plain,
    ( sK1 != sK1
    | sK3 = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_xboole_0 = sK2
    | k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4)) ),
    inference(duplicate_literal_removal,[],[f335])).

fof(f335,plain,
    ( sK1 != sK1
    | sK3 = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_xboole_0 = sK2
    | k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f308,f261])).

fof(f308,plain,(
    ! [X4] :
      ( sK1 != k1_relat_1(X4)
      | sK3 = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k1_xboole_0 = sK2
      | k1_funct_1(sK3,sK5(sK3,X4)) = k1_funct_1(sK4,sK5(sK3,X4)) ) ),
    inference(resolution,[],[f290,f60])).

fof(f60,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f290,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK3,X0),sK1)
      | k1_relat_1(X0) != sK1
      | sK3 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = sK2 ) ),
    inference(global_subsumption,[],[f54,f102,f284])).

fof(f284,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != sK1
      | r2_hidden(sK5(sK3,X0),sK1)
      | sK3 = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f64,f259])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f103,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f76,f59])).

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f181,plain,(
    r2_relset_1(sK1,sK2,sK3,sK3) ),
    inference(resolution,[],[f127,f56])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f559,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f521,f550])).

fof(f550,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f537,f99])).

fof(f537,plain,(
    v1_xboole_0(sK3) ),
    inference(resolution,[],[f530,f129])).

fof(f530,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f518,f88])).

fof(f518,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f56,f516])).

fof(f521,plain,(
    ~ r2_relset_1(sK1,k1_xboole_0,sK3,sK4) ),
    inference(backward_demodulation,[],[f61,f516])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:37:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.47  % (29797)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.48  % (29789)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (29777)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (29789)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (29801)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f622,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(resolution,[],[f607,f180])).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_relset_1(X0,X1,k1_xboole_0,k1_xboole_0)) )),
% 0.22/0.52    inference(resolution,[],[f127,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f95,f121])).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~sP7(X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f96,f63])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP7(X1,X0)) )),
% 0.22/0.52    inference(general_splitting,[],[f87,f95_D])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP7(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f95_D])).
% 0.22/0.52  fof(f95_D,plain,(
% 0.22/0.52    ( ! [X0,X1] : (( ! [X2] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) <=> ~sP7(X1,X0)) )),
% 0.22/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 0.22/0.52  fof(f607,plain,(
% 0.22/0.52    ~r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    inference(backward_demodulation,[],[f559,f594])).
% 0.22/0.52  fof(f594,plain,(
% 0.22/0.52    k1_xboole_0 = sK4),
% 0.22/0.52    inference(resolution,[],[f581,f99])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(resolution,[],[f72,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.22/0.52  fof(f581,plain,(
% 0.22/0.52    v1_xboole_0(sK4)),
% 0.22/0.52    inference(resolution,[],[f531,f129])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f128,f88])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.52    inference(flattening,[],[f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f67,f62])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.22/0.52  fof(f531,plain,(
% 0.22/0.52    m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.52    inference(forward_demodulation,[],[f520,f88])).
% 0.22/0.52  fof(f520,plain,(
% 0.22/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.22/0.52    inference(backward_demodulation,[],[f59,f516])).
% 0.22/0.52  fof(f516,plain,(
% 0.22/0.52    k1_xboole_0 = sK2),
% 0.22/0.52    inference(global_subsumption,[],[f181,f484])).
% 0.22/0.52  fof(f484,plain,(
% 0.22/0.52    ~r2_relset_1(sK1,sK2,sK3,sK3) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(superposition,[],[f61,f480])).
% 0.22/0.52  fof(f480,plain,(
% 0.22/0.52    sK3 = sK4 | k1_xboole_0 = sK2),
% 0.22/0.52    inference(global_subsumption,[],[f57,f103,f338,f479])).
% 0.22/0.52  fof(f479,plain,(
% 0.22/0.52    k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4)) | sK3 = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f478])).
% 0.22/0.52  fof(f478,plain,(
% 0.22/0.52    sK1 != sK1 | k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4)) | sK3 = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f477])).
% 0.22/0.52  fof(f477,plain,(
% 0.22/0.52    sK1 != sK1 | k1_funct_1(sK3,sK5(sK3,sK4)) != k1_funct_1(sK4,sK5(sK3,sK4)) | sK3 = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 0.22/0.52    inference(superposition,[],[f472,f261])).
% 0.22/0.52  fof(f261,plain,(
% 0.22/0.52    sK1 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(global_subsumption,[],[f58,f260])).
% 0.22/0.52  fof(f260,plain,(
% 0.22/0.52    sK1 = k1_relat_1(sK4) | ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(forward_demodulation,[],[f255,f211])).
% 0.22/0.52  fof(f211,plain,(
% 0.22/0.52    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4)),
% 0.22/0.52    inference(resolution,[],[f77,f59])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.52  fof(f255,plain,(
% 0.22/0.52    ~v1_funct_2(sK4,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4)),
% 0.22/0.52    inference(resolution,[],[f79,f151])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    sP0(sK1,sK4,sK2)),
% 0.22/0.52    inference(resolution,[],[f83,f59])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(definition_folding,[],[f33,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(flattening,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 0.22/0.52    inference(rectify,[],[f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f38])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    v1_funct_2(sK4,sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f21,f41,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (~r2_relset_1(sK1,sK2,sK3,sK4) & ! [X4] : (k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4) | ~r2_hidden(X4,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.22/0.52    inference(negated_conjecture,[],[f16])).
% 0.22/0.52  fof(f16,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 0.22/0.52  fof(f472,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(X0) != sK1 | k1_funct_1(sK3,sK5(sK3,X0)) != k1_funct_1(X0,sK5(sK3,X0)) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = sK2) )),
% 0.22/0.52    inference(global_subsumption,[],[f54,f102,f466])).
% 0.22/0.52  fof(f466,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(X0) != sK1 | k1_funct_1(sK3,sK5(sK3,X0)) != k1_funct_1(X0,sK5(sK3,X0)) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2) )),
% 0.22/0.52    inference(superposition,[],[f65,f259])).
% 0.22/0.52  fof(f259,plain,(
% 0.22/0.52    sK1 = k1_relat_1(sK3) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(global_subsumption,[],[f55,f258])).
% 0.22/0.52  fof(f258,plain,(
% 0.22/0.52    sK1 = k1_relat_1(sK3) | ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(forward_demodulation,[],[f254,f210])).
% 0.22/0.52  fof(f210,plain,(
% 0.22/0.52    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 0.22/0.52    inference(resolution,[],[f77,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f254,plain,(
% 0.22/0.52    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.22/0.52    inference(resolution,[],[f79,f150])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    sP0(sK1,sK3,sK2)),
% 0.22/0.52    inference(resolution,[],[f83,f56])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    v1_funct_2(sK3,sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    v1_relat_1(sK3)),
% 0.22/0.52    inference(resolution,[],[f76,f56])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    v1_funct_1(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f338,plain,(
% 0.22/0.52    k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4)) | k1_xboole_0 = sK2 | sK3 = sK4),
% 0.22/0.52    inference(global_subsumption,[],[f57,f103,f337])).
% 0.22/0.52  fof(f337,plain,(
% 0.22/0.52    sK3 = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_xboole_0 = sK2 | k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4))),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f336])).
% 0.22/0.52  fof(f336,plain,(
% 0.22/0.52    sK1 != sK1 | sK3 = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_xboole_0 = sK2 | k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4))),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f335])).
% 0.22/0.52  fof(f335,plain,(
% 0.22/0.52    sK1 != sK1 | sK3 = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | k1_xboole_0 = sK2 | k1_funct_1(sK3,sK5(sK3,sK4)) = k1_funct_1(sK4,sK5(sK3,sK4)) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(superposition,[],[f308,f261])).
% 0.22/0.52  fof(f308,plain,(
% 0.22/0.52    ( ! [X4] : (sK1 != k1_relat_1(X4) | sK3 = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k1_xboole_0 = sK2 | k1_funct_1(sK3,sK5(sK3,X4)) = k1_funct_1(sK4,sK5(sK3,X4))) )),
% 0.22/0.52    inference(resolution,[],[f290,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X4] : (~r2_hidden(X4,sK1) | k1_funct_1(sK3,X4) = k1_funct_1(sK4,X4)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f290,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK5(sK3,X0),sK1) | k1_relat_1(X0) != sK1 | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = sK2) )),
% 0.22/0.52    inference(global_subsumption,[],[f54,f102,f284])).
% 0.22/0.52  fof(f284,plain,(
% 0.22/0.52    ( ! [X0] : (k1_relat_1(X0) != sK1 | r2_hidden(sK5(sK3,X0),sK1) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_xboole_0 = sK2) )),
% 0.22/0.52    inference(superposition,[],[f64,f259])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f44])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    v1_relat_1(sK4)),
% 0.22/0.52    inference(resolution,[],[f76,f59])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    v1_funct_1(sK4)),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ~r2_relset_1(sK1,sK2,sK3,sK4)),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f181,plain,(
% 0.22/0.52    r2_relset_1(sK1,sK2,sK3,sK3)),
% 0.22/0.52    inference(resolution,[],[f127,f56])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.52    inference(cnf_transformation,[],[f42])).
% 0.22/0.52  fof(f559,plain,(
% 0.22/0.52    ~r2_relset_1(sK1,k1_xboole_0,k1_xboole_0,sK4)),
% 0.22/0.52    inference(backward_demodulation,[],[f521,f550])).
% 0.22/0.52  fof(f550,plain,(
% 0.22/0.52    k1_xboole_0 = sK3),
% 0.22/0.52    inference(resolution,[],[f537,f99])).
% 0.22/0.52  fof(f537,plain,(
% 0.22/0.52    v1_xboole_0(sK3)),
% 0.22/0.52    inference(resolution,[],[f530,f129])).
% 0.22/0.52  fof(f530,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.52    inference(forward_demodulation,[],[f518,f88])).
% 0.22/0.52  fof(f518,plain,(
% 0.22/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 0.22/0.52    inference(backward_demodulation,[],[f56,f516])).
% 0.22/0.52  fof(f521,plain,(
% 0.22/0.52    ~r2_relset_1(sK1,k1_xboole_0,sK3,sK4)),
% 0.22/0.52    inference(backward_demodulation,[],[f61,f516])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (29789)------------------------------
% 0.22/0.52  % (29789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (29789)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (29789)Memory used [KB]: 6524
% 0.22/0.52  % (29789)Time elapsed: 0.076 s
% 0.22/0.52  % (29789)------------------------------
% 0.22/0.52  % (29789)------------------------------
% 0.22/0.53  % (29782)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (29776)Success in time 0.167 s
%------------------------------------------------------------------------------
