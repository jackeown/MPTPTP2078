%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 537 expanded)
%              Number of leaves         :   30 ( 146 expanded)
%              Depth                    :   27
%              Number of atoms          :  513 (1488 expanded)
%              Number of equality atoms :  108 ( 519 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f961,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f255,f293,f699,f730,f751,f755,f960])).

fof(f960,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f959])).

fof(f959,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f958,f91])).

fof(f91,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f90,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f90,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f57,f49])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
      | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
          | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f958,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f957,f112])).

fof(f112,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f75,f49])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f957,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(resolution,[],[f954,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f954,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(resolution,[],[f953,f52])).

fof(f52,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f953,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(k6_relat_1(k2_relat_1(sK2)),X0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f952,f51])).

fof(f51,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f952,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(k6_relat_1(k2_relat_1(sK2)),X0)
        | ~ v1_relat_1(k6_relat_1(k2_relat_1(sK2)))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(resolution,[],[f947,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X1)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

fof(f947,plain,
    ( ~ v4_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(trivial_inequality_removal,[],[f946])).

fof(f946,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v4_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(superposition,[],[f331,f915])).

fof(f915,plain,
    ( ! [X0] :
        ( k1_relat_1(sK2) = k10_relat_1(sK2,X0)
        | ~ v4_relat_1(k6_relat_1(k2_relat_1(sK2)),X0) )
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f914,f91])).

fof(f914,plain,
    ( ! [X0] :
        ( k1_relat_1(sK2) = k10_relat_1(sK2,X0)
        | ~ v4_relat_1(k6_relat_1(k2_relat_1(sK2)),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f891,f111])).

fof(f111,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f74,f49])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f891,plain,
    ( ! [X0] :
        ( k1_relat_1(sK2) = k10_relat_1(sK2,X0)
        | ~ v4_relat_1(k6_relat_1(k2_relat_1(sK2)),X0)
        | ~ v4_relat_1(sK2,sK0)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(superposition,[],[f878,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f878,plain,
    ( ! [X1] :
        ( k1_relat_1(sK2) = k10_relat_1(k7_relat_1(sK2,sK0),X1)
        | ~ v4_relat_1(k6_relat_1(k2_relat_1(sK2)),X1) )
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f649,f826])).

fof(f826,plain,
    ( k1_relat_1(sK2) = k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f656,f823])).

fof(f823,plain,
    ( k1_relat_1(sK2) = k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK0)))
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f822,f682])).

fof(f682,plain,
    ( v4_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f681])).

fof(f681,plain,
    ( spl3_7
  <=> v4_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f822,plain,
    ( k1_relat_1(sK2) = k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK0)))
    | ~ v4_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f814,f272])).

fof(f272,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl3_3
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f814,plain,
    ( k1_relat_1(sK2) = k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK0)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v4_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(superposition,[],[f783,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k9_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f62,f68])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f783,plain,
    ( k1_relat_1(sK2) = k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(sK2)))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f764,f272])).

fof(f764,plain,
    ( k1_relat_1(sK2) = k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(sK2)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl3_11 ),
    inference(superposition,[],[f365,f744])).

fof(f744,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f742])).

fof(f742,plain,
    ( spl3_11
  <=> k1_relat_1(sK2) = k1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f365,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k9_relat_1(X0,k1_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f364,f79])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f364,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k9_relat_1(X0,k1_relat_1(X0)))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f354])).

fof(f354,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k9_relat_1(X0,k1_relat_1(X0)))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f108,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f108,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2))
      | k1_relat_1(X1) = k10_relat_1(X1,X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f71,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f656,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(sK2)) = k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK0)))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f652,f272])).

fof(f652,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(sK2)) = k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK0)))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f647,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,X1) = k10_relat_1(X0,k3_xboole_0(X1,k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f63,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f647,plain,
    ( ! [X6] : k10_relat_1(k7_relat_1(sK2,sK0),X6) = k10_relat_1(k7_relat_1(sK2,sK0),k3_xboole_0(k2_relat_1(sK2),X6))
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f646,f91])).

% (10585)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f646,plain,
    ( ! [X6] :
        ( k10_relat_1(k7_relat_1(sK2,sK0),X6) = k10_relat_1(k7_relat_1(sK2,sK0),k3_xboole_0(k2_relat_1(sK2),X6))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f631,f272])).

fof(f631,plain,
    ( ! [X6] :
        ( k10_relat_1(k7_relat_1(sK2,sK0),X6) = k10_relat_1(k7_relat_1(sK2,sK0),k3_xboole_0(k2_relat_1(sK2),X6))
        | ~ v1_relat_1(k7_relat_1(sK2,sK0))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_1 ),
    inference(superposition,[],[f119,f263])).

fof(f263,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f261,f49])).

fof(f261,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(superposition,[],[f258,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f258,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k9_relat_1(sK2,sK0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f256,f49])).

fof(f256,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k9_relat_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(superposition,[],[f83,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f83,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_1
  <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f119,plain,(
    ! [X4,X2,X3] :
      ( k10_relat_1(k7_relat_1(X2,X3),X4) = k10_relat_1(k7_relat_1(X2,X3),k3_xboole_0(k9_relat_1(X2,X3),X4))
      | ~ v1_relat_1(k7_relat_1(X2,X3))
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f63,f62])).

% (10602)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f649,plain,
    ( ! [X1] :
        ( k10_relat_1(k7_relat_1(sK2,sK0),X1) = k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(sK2))
        | ~ v4_relat_1(k6_relat_1(k2_relat_1(sK2)),X1) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f647,f162])).

fof(f162,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = X2
      | ~ v4_relat_1(k6_relat_1(X2),X3) ) ),
    inference(forward_demodulation,[],[f161,f55])).

fof(f55,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f161,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = k2_relat_1(k6_relat_1(X2))
      | ~ v4_relat_1(k6_relat_1(X2),X3) ) ),
    inference(subsumption_resolution,[],[f159,f51])).

fof(f159,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = k2_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v4_relat_1(k6_relat_1(X2),X3) ) ),
    inference(superposition,[],[f158,f117])).

fof(f158,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_demodulation,[],[f157,f55])).

fof(f157,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f156,f55])).

fof(f156,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) ),
    inference(subsumption_resolution,[],[f155,f51])).

fof(f155,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f149,f51])).

fof(f149,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f56,f60])).

fof(f60,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f331,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK1)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f330,f49])).

fof(f330,plain,
    ( k1_relat_1(sK2) != k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_2 ),
    inference(superposition,[],[f329,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f329,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1)
    | spl3_2 ),
    inference(subsumption_resolution,[],[f328,f49])).

fof(f328,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_2 ),
    inference(superposition,[],[f88,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f88,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_2
  <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f755,plain,
    ( spl3_11
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f754,f738,f685,f742])).

fof(f685,plain,
    ( spl3_8
  <=> r1_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f738,plain,
    ( spl3_10
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f754,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f752,f686])).

fof(f686,plain,
    ( r1_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f685])).

fof(f752,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k7_relat_1(sK2,sK0))
    | ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK0)))
    | ~ spl3_10 ),
    inference(resolution,[],[f739,f71])).

fof(f739,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),k1_relat_1(sK2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f738])).

fof(f751,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f750])).

fof(f750,plain,
    ( $false
    | spl3_10 ),
    inference(subsumption_resolution,[],[f749,f91])).

fof(f749,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_10 ),
    inference(subsumption_resolution,[],[f748,f111])).

fof(f748,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_10 ),
    inference(subsumption_resolution,[],[f747,f79])).

fof(f747,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_10 ),
    inference(superposition,[],[f740,f68])).

fof(f740,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),k1_relat_1(sK2))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f738])).

fof(f730,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f729])).

fof(f729,plain,
    ( $false
    | spl3_8 ),
    inference(subsumption_resolution,[],[f728,f91])).

fof(f728,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_8 ),
    inference(subsumption_resolution,[],[f727,f111])).

fof(f727,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_8 ),
    inference(subsumption_resolution,[],[f726,f79])).

fof(f726,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_8 ),
    inference(superposition,[],[f687,f68])).

fof(f687,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f685])).

fof(f699,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f698])).

fof(f698,plain,
    ( $false
    | spl3_7 ),
    inference(subsumption_resolution,[],[f697,f91])).

fof(f697,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(subsumption_resolution,[],[f696,f111])).

fof(f696,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(subsumption_resolution,[],[f694,f348])).

fof(f348,plain,(
    v4_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(resolution,[],[f345,f79])).

fof(f345,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v4_relat_1(sK2,X0) ) ),
    inference(resolution,[],[f339,f49])).

fof(f339,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ r1_tarski(k1_relat_1(X4),X5)
      | v4_relat_1(X4,X5) ) ),
    inference(resolution,[],[f78,f74])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f694,plain,
    ( ~ v4_relat_1(sK2,k1_relat_1(sK2))
    | ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(superposition,[],[f683,f68])).

fof(f683,plain,
    ( ~ v4_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(sK2))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f681])).

fof(f293,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f291,f111])).

fof(f291,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f290,f91])).

fof(f290,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | spl3_3 ),
    inference(duplicate_literal_removal,[],[f289])).

fof(f289,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(superposition,[],[f273,f68])).

fof(f273,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f271])).

fof(f255,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f253,f111])).

fof(f253,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f252,f91])).

fof(f252,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f251])).

fof(f251,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | spl3_1 ),
    inference(superposition,[],[f250,f117])).

fof(f250,plain,
    ( k9_relat_1(sK2,sK0) != k2_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f249,f49])).

fof(f249,plain,
    ( k9_relat_1(sK2,sK0) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_1 ),
    inference(superposition,[],[f248,f73])).

fof(f248,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f247,f49])).

fof(f247,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_1 ),
    inference(superposition,[],[f84,f76])).

fof(f84,plain,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f89,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f50,f86,f82])).

fof(f50,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:09:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.40  % (10588)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.48  % (10581)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.49  % (10594)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.50  % (10583)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (10583)Refutation not found, incomplete strategy% (10583)------------------------------
% 0.22/0.50  % (10583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (10583)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (10583)Memory used [KB]: 10618
% 0.22/0.50  % (10583)Time elapsed: 0.087 s
% 0.22/0.50  % (10583)------------------------------
% 0.22/0.50  % (10583)------------------------------
% 0.22/0.50  % (10587)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.50  % (10591)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (10580)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (10595)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.51  % (10589)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (10597)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (10586)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (10582)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (10600)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (10598)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (10584)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (10599)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (10593)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (10582)Refutation not found, incomplete strategy% (10582)------------------------------
% 0.22/0.53  % (10582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10582)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (10582)Memory used [KB]: 6268
% 0.22/0.53  % (10582)Time elapsed: 0.079 s
% 0.22/0.53  % (10582)------------------------------
% 0.22/0.53  % (10582)------------------------------
% 0.22/0.53  % (10581)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f961,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f89,f255,f293,f699,f730,f751,f755,f960])).
% 0.22/0.53  fof(f960,plain,(
% 0.22/0.53    ~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f959])).
% 0.22/0.53  fof(f959,plain,(
% 0.22/0.53    $false | (~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f958,f91])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    v1_relat_1(sK2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f90,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f57,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    (k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.22/0.53    inference(negated_conjecture,[],[f22])).
% 0.22/0.53  fof(f22,conjecture,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.53  fof(f958,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | (~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f957,f112])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    v5_relat_1(sK2,sK1)),
% 0.22/0.53    inference(resolution,[],[f75,f49])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.53  fof(f957,plain,(
% 0.22/0.53    ~v5_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | (~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.22/0.53    inference(resolution,[],[f954,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.53  fof(f954,plain,(
% 0.22/0.53    ~r1_tarski(k2_relat_1(sK2),sK1) | (~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.22/0.53    inference(resolution,[],[f953,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
% 0.22/0.53  fof(f953,plain,(
% 0.22/0.53    ( ! [X0] : (~v4_relat_1(k6_relat_1(k2_relat_1(sK2)),X0) | ~r1_tarski(X0,sK1)) ) | (~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f952,f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f952,plain,(
% 0.22/0.53    ( ! [X0] : (~v4_relat_1(k6_relat_1(k2_relat_1(sK2)),X0) | ~v1_relat_1(k6_relat_1(k2_relat_1(sK2))) | ~r1_tarski(X0,sK1)) ) | (~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.22/0.53    inference(resolution,[],[f947,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | ~v4_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X1) | (~v4_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).
% 0.22/0.53  fof(f947,plain,(
% 0.22/0.53    ~v4_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) | (~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f946])).
% 0.22/0.53  fof(f946,plain,(
% 0.22/0.53    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v4_relat_1(k6_relat_1(k2_relat_1(sK2)),sK1) | (~spl3_1 | spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.22/0.53    inference(superposition,[],[f331,f915])).
% 0.22/0.53  fof(f915,plain,(
% 0.22/0.53    ( ! [X0] : (k1_relat_1(sK2) = k10_relat_1(sK2,X0) | ~v4_relat_1(k6_relat_1(k2_relat_1(sK2)),X0)) ) | (~spl3_1 | ~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f914,f91])).
% 0.22/0.53  fof(f914,plain,(
% 0.22/0.53    ( ! [X0] : (k1_relat_1(sK2) = k10_relat_1(sK2,X0) | ~v4_relat_1(k6_relat_1(k2_relat_1(sK2)),X0) | ~v1_relat_1(sK2)) ) | (~spl3_1 | ~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f891,f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    v4_relat_1(sK2,sK0)),
% 0.22/0.53    inference(resolution,[],[f74,f49])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f891,plain,(
% 0.22/0.53    ( ! [X0] : (k1_relat_1(sK2) = k10_relat_1(sK2,X0) | ~v4_relat_1(k6_relat_1(k2_relat_1(sK2)),X0) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2)) ) | (~spl3_1 | ~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.22/0.53    inference(superposition,[],[f878,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.53  fof(f878,plain,(
% 0.22/0.53    ( ! [X1] : (k1_relat_1(sK2) = k10_relat_1(k7_relat_1(sK2,sK0),X1) | ~v4_relat_1(k6_relat_1(k2_relat_1(sK2)),X1)) ) | (~spl3_1 | ~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.22/0.53    inference(forward_demodulation,[],[f649,f826])).
% 0.22/0.53  fof(f826,plain,(
% 0.22/0.53    k1_relat_1(sK2) = k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.22/0.53    inference(backward_demodulation,[],[f656,f823])).
% 0.22/0.53  fof(f823,plain,(
% 0.22/0.53    k1_relat_1(sK2) = k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK0))) | (~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f822,f682])).
% 0.22/0.53  fof(f682,plain,(
% 0.22/0.53    v4_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(sK2)) | ~spl3_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f681])).
% 0.22/0.53  fof(f681,plain,(
% 0.22/0.53    spl3_7 <=> v4_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.53  fof(f822,plain,(
% 0.22/0.53    k1_relat_1(sK2) = k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK0))) | ~v4_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(sK2)) | (~spl3_3 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f814,f272])).
% 0.22/0.53  fof(f272,plain,(
% 0.22/0.53    v1_relat_1(k7_relat_1(sK2,sK0)) | ~spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f271])).
% 0.22/0.53  fof(f271,plain,(
% 0.22/0.53    spl3_3 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f814,plain,(
% 0.22/0.53    k1_relat_1(sK2) = k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK0))) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v4_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(sK2)) | (~spl3_3 | ~spl3_11)),
% 0.22/0.53    inference(superposition,[],[f783,f117])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f116])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relat_1(X0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(superposition,[],[f62,f68])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.53  fof(f783,plain,(
% 0.22/0.53    k1_relat_1(sK2) = k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(sK2))) | (~spl3_3 | ~spl3_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f764,f272])).
% 0.22/0.53  fof(f764,plain,(
% 0.22/0.53    k1_relat_1(sK2) = k10_relat_1(k7_relat_1(sK2,sK0),k9_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(sK2))) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~spl3_11),
% 0.22/0.53    inference(superposition,[],[f365,f744])).
% 0.22/0.53  fof(f744,plain,(
% 0.22/0.53    k1_relat_1(sK2) = k1_relat_1(k7_relat_1(sK2,sK0)) | ~spl3_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f742])).
% 0.22/0.53  fof(f742,plain,(
% 0.22/0.53    spl3_11 <=> k1_relat_1(sK2) = k1_relat_1(k7_relat_1(sK2,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.53  fof(f365,plain,(
% 0.22/0.53    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k9_relat_1(X0,k1_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f364,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f364,plain,(
% 0.22/0.53    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k9_relat_1(X0,k1_relat_1(X0))) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X0))) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f354])).
% 0.22/0.53  fof(f354,plain,(
% 0.22/0.53    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k9_relat_1(X0,k1_relat_1(X0))) | ~v1_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(resolution,[],[f108,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2)) | k1_relat_1(X1) = k10_relat_1(X1,X2) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(resolution,[],[f71,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f48])).
% 0.22/0.53  fof(f656,plain,(
% 0.22/0.53    k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(sK2)) = k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK0))) | (~spl3_1 | ~spl3_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f652,f272])).
% 0.22/0.53  fof(f652,plain,(
% 0.22/0.53    k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(sK2)) = k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK0))) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | (~spl3_1 | ~spl3_3)),
% 0.22/0.53    inference(superposition,[],[f647,f120])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k10_relat_1(X0,X1) = k10_relat_1(X0,k3_xboole_0(X1,k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(superposition,[],[f63,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 0.22/0.53  fof(f647,plain,(
% 0.22/0.53    ( ! [X6] : (k10_relat_1(k7_relat_1(sK2,sK0),X6) = k10_relat_1(k7_relat_1(sK2,sK0),k3_xboole_0(k2_relat_1(sK2),X6))) ) | (~spl3_1 | ~spl3_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f646,f91])).
% 0.22/0.53  % (10585)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  fof(f646,plain,(
% 0.22/0.53    ( ! [X6] : (k10_relat_1(k7_relat_1(sK2,sK0),X6) = k10_relat_1(k7_relat_1(sK2,sK0),k3_xboole_0(k2_relat_1(sK2),X6)) | ~v1_relat_1(sK2)) ) | (~spl3_1 | ~spl3_3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f631,f272])).
% 0.22/0.53  fof(f631,plain,(
% 0.22/0.53    ( ! [X6] : (k10_relat_1(k7_relat_1(sK2,sK0),X6) = k10_relat_1(k7_relat_1(sK2,sK0),k3_xboole_0(k2_relat_1(sK2),X6)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2)) ) | ~spl3_1),
% 0.22/0.53    inference(superposition,[],[f119,f263])).
% 0.22/0.53  fof(f263,plain,(
% 0.22/0.53    k9_relat_1(sK2,sK0) = k2_relat_1(sK2) | ~spl3_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f261,f49])).
% 0.22/0.53  fof(f261,plain,(
% 0.22/0.53    k9_relat_1(sK2,sK0) = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_1),
% 0.22/0.53    inference(superposition,[],[f258,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.53  fof(f258,plain,(
% 0.22/0.53    k2_relset_1(sK0,sK1,sK2) = k9_relat_1(sK2,sK0) | ~spl3_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f256,f49])).
% 0.22/0.53  fof(f256,plain,(
% 0.22/0.53    k2_relset_1(sK0,sK1,sK2) = k9_relat_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl3_1),
% 0.22/0.53    inference(superposition,[],[f83,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0) | ~spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl3_1 <=> k2_relset_1(sK0,sK1,sK2) = k7_relset_1(sK0,sK1,sK2,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X4,X2,X3] : (k10_relat_1(k7_relat_1(X2,X3),X4) = k10_relat_1(k7_relat_1(X2,X3),k3_xboole_0(k9_relat_1(X2,X3),X4)) | ~v1_relat_1(k7_relat_1(X2,X3)) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(superposition,[],[f63,f62])).
% 0.22/0.53  % (10602)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.53  fof(f649,plain,(
% 0.22/0.53    ( ! [X1] : (k10_relat_1(k7_relat_1(sK2,sK0),X1) = k10_relat_1(k7_relat_1(sK2,sK0),k2_relat_1(sK2)) | ~v4_relat_1(k6_relat_1(k2_relat_1(sK2)),X1)) ) | (~spl3_1 | ~spl3_3)),
% 0.22/0.53    inference(superposition,[],[f647,f162])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = X2 | ~v4_relat_1(k6_relat_1(X2),X3)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f161,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k2_relat_1(k6_relat_1(X2)) | ~v4_relat_1(k6_relat_1(X2),X3)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f159,f51])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k2_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X2)) | ~v4_relat_1(k6_relat_1(X2),X3)) )),
% 0.22/0.53    inference(superposition,[],[f158,f117])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),X0)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f157,f55])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0)))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f156,f55])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f155,f51])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f149,f51])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X1),k2_relat_1(k6_relat_1(X0))) = k2_relat_1(k6_relat_1(k3_xboole_0(X1,X0))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.53    inference(superposition,[],[f56,f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.22/0.53  fof(f331,plain,(
% 0.22/0.53    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) | spl3_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f330,f49])).
% 0.22/0.53  fof(f330,plain,(
% 0.22/0.53    k1_relat_1(sK2) != k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_2),
% 0.22/0.53    inference(superposition,[],[f329,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.53  fof(f329,plain,(
% 0.22/0.53    k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1) | spl3_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f328,f49])).
% 0.22/0.53  fof(f328,plain,(
% 0.22/0.53    k1_relset_1(sK0,sK1,sK2) != k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_2),
% 0.22/0.53    inference(superposition,[],[f88,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl3_2 <=> k1_relset_1(sK0,sK1,sK2) = k8_relset_1(sK0,sK1,sK2,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f755,plain,(
% 0.22/0.53    spl3_11 | ~spl3_8 | ~spl3_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f754,f738,f685,f742])).
% 0.22/0.53  fof(f685,plain,(
% 0.22/0.53    spl3_8 <=> r1_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.53  fof(f738,plain,(
% 0.22/0.53    spl3_10 <=> r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),k1_relat_1(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.53  fof(f754,plain,(
% 0.22/0.53    k1_relat_1(sK2) = k1_relat_1(k7_relat_1(sK2,sK0)) | (~spl3_8 | ~spl3_10)),
% 0.22/0.53    inference(subsumption_resolution,[],[f752,f686])).
% 0.22/0.53  fof(f686,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK0))) | ~spl3_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f685])).
% 0.22/0.53  fof(f752,plain,(
% 0.22/0.53    k1_relat_1(sK2) = k1_relat_1(k7_relat_1(sK2,sK0)) | ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK0))) | ~spl3_10),
% 0.22/0.53    inference(resolution,[],[f739,f71])).
% 0.22/0.53  fof(f739,plain,(
% 0.22/0.53    r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),k1_relat_1(sK2)) | ~spl3_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f738])).
% 0.22/0.53  fof(f751,plain,(
% 0.22/0.53    spl3_10),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f750])).
% 0.22/0.53  fof(f750,plain,(
% 0.22/0.53    $false | spl3_10),
% 0.22/0.53    inference(subsumption_resolution,[],[f749,f91])).
% 0.22/0.53  fof(f749,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | spl3_10),
% 0.22/0.53    inference(subsumption_resolution,[],[f748,f111])).
% 0.22/0.53  fof(f748,plain,(
% 0.22/0.53    ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl3_10),
% 0.22/0.53    inference(subsumption_resolution,[],[f747,f79])).
% 0.22/0.53  fof(f747,plain,(
% 0.22/0.53    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl3_10),
% 0.22/0.53    inference(superposition,[],[f740,f68])).
% 0.22/0.53  fof(f740,plain,(
% 0.22/0.53    ~r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),k1_relat_1(sK2)) | spl3_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f738])).
% 0.22/0.53  fof(f730,plain,(
% 0.22/0.53    spl3_8),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f729])).
% 0.22/0.53  fof(f729,plain,(
% 0.22/0.53    $false | spl3_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f728,f91])).
% 0.22/0.53  fof(f728,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | spl3_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f727,f111])).
% 0.22/0.53  fof(f727,plain,(
% 0.22/0.53    ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl3_8),
% 0.22/0.53    inference(subsumption_resolution,[],[f726,f79])).
% 0.22/0.53  fof(f726,plain,(
% 0.22/0.53    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl3_8),
% 0.22/0.53    inference(superposition,[],[f687,f68])).
% 0.22/0.53  fof(f687,plain,(
% 0.22/0.53    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK0))) | spl3_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f685])).
% 0.22/0.53  fof(f699,plain,(
% 0.22/0.53    spl3_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f698])).
% 0.22/0.53  fof(f698,plain,(
% 0.22/0.53    $false | spl3_7),
% 0.22/0.53    inference(subsumption_resolution,[],[f697,f91])).
% 0.22/0.53  fof(f697,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | spl3_7),
% 0.22/0.53    inference(subsumption_resolution,[],[f696,f111])).
% 0.22/0.53  fof(f696,plain,(
% 0.22/0.53    ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl3_7),
% 0.22/0.53    inference(subsumption_resolution,[],[f694,f348])).
% 0.22/0.53  fof(f348,plain,(
% 0.22/0.53    v4_relat_1(sK2,k1_relat_1(sK2))),
% 0.22/0.53    inference(resolution,[],[f345,f79])).
% 0.22/0.53  fof(f345,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v4_relat_1(sK2,X0)) )),
% 0.22/0.53    inference(resolution,[],[f339,f49])).
% 0.22/0.53  fof(f339,plain,(
% 0.22/0.53    ( ! [X6,X4,X7,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~r1_tarski(k1_relat_1(X4),X5) | v4_relat_1(X4,X5)) )),
% 0.22/0.53    inference(resolution,[],[f78,f74])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.53    inference(flattening,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.22/0.53    inference(ennf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 0.22/0.53  fof(f694,plain,(
% 0.22/0.53    ~v4_relat_1(sK2,k1_relat_1(sK2)) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl3_7),
% 0.22/0.53    inference(superposition,[],[f683,f68])).
% 0.22/0.53  fof(f683,plain,(
% 0.22/0.53    ~v4_relat_1(k7_relat_1(sK2,sK0),k1_relat_1(sK2)) | spl3_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f681])).
% 0.22/0.53  fof(f293,plain,(
% 0.22/0.53    spl3_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f292])).
% 0.22/0.53  fof(f292,plain,(
% 0.22/0.53    $false | spl3_3),
% 0.22/0.53    inference(subsumption_resolution,[],[f291,f111])).
% 0.22/0.53  fof(f291,plain,(
% 0.22/0.53    ~v4_relat_1(sK2,sK0) | spl3_3),
% 0.22/0.53    inference(subsumption_resolution,[],[f290,f91])).
% 0.22/0.53  fof(f290,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | spl3_3),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f289])).
% 0.22/0.53  fof(f289,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl3_3),
% 0.22/0.53    inference(superposition,[],[f273,f68])).
% 0.22/0.53  fof(f273,plain,(
% 0.22/0.53    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f271])).
% 0.22/0.53  fof(f255,plain,(
% 0.22/0.53    spl3_1),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f254])).
% 0.22/0.53  fof(f254,plain,(
% 0.22/0.53    $false | spl3_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f253,f111])).
% 0.22/0.53  fof(f253,plain,(
% 0.22/0.53    ~v4_relat_1(sK2,sK0) | spl3_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f252,f91])).
% 0.22/0.53  fof(f252,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | spl3_1),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f251])).
% 0.22/0.53  fof(f251,plain,(
% 0.22/0.53    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | spl3_1),
% 0.22/0.53    inference(superposition,[],[f250,f117])).
% 0.22/0.53  fof(f250,plain,(
% 0.22/0.53    k9_relat_1(sK2,sK0) != k2_relat_1(sK2) | spl3_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f249,f49])).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    k9_relat_1(sK2,sK0) != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_1),
% 0.22/0.53    inference(superposition,[],[f248,f73])).
% 0.22/0.53  fof(f248,plain,(
% 0.22/0.53    k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0) | spl3_1),
% 0.22/0.53    inference(subsumption_resolution,[],[f247,f49])).
% 0.22/0.53  fof(f247,plain,(
% 0.22/0.53    k2_relset_1(sK0,sK1,sK2) != k9_relat_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl3_1),
% 0.22/0.53    inference(superposition,[],[f84,f76])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) | spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f82])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ~spl3_1 | ~spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f50,f86,f82])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (10581)------------------------------
% 0.22/0.53  % (10581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10581)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (10581)Memory used [KB]: 6652
% 0.22/0.53  % (10581)Time elapsed: 0.115 s
% 0.22/0.53  % (10581)------------------------------
% 0.22/0.53  % (10581)------------------------------
% 0.22/0.53  % (10576)Success in time 0.167 s
%------------------------------------------------------------------------------
