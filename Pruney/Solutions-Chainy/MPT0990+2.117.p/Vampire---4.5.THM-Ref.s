%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:48 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 990 expanded)
%              Number of leaves         :   28 ( 306 expanded)
%              Depth                    :   25
%              Number of atoms          :  523 (8561 expanded)
%              Number of equality atoms :  150 (2858 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1720,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f243,f1065,f1085,f1718])).

fof(f1718,plain,
    ( ~ spl4_7
    | ~ spl4_61 ),
    inference(avatar_contradiction_clause,[],[f1717])).

fof(f1717,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_61 ),
    inference(subsumption_resolution,[],[f1715,f69])).

fof(f69,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f52,f51])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
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
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
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

fof(f1715,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ spl4_7
    | ~ spl4_61 ),
    inference(backward_demodulation,[],[f1094,f1714])).

fof(f1714,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_7
    | ~ spl4_61 ),
    inference(forward_demodulation,[],[f1713,f1168])).

fof(f1168,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_61 ),
    inference(backward_demodulation,[],[f203,f1166])).

fof(f1166,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_61 ),
    inference(forward_demodulation,[],[f1042,f1093])).

fof(f1093,plain,
    ( sK1 = k9_relat_1(sK2,sK0)
    | ~ spl4_61 ),
    inference(backward_demodulation,[],[f345,f1060])).

fof(f1060,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f1058])).

fof(f1058,plain,
    ( spl4_61
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f345,plain,(
    sK1 = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f341,f269])).

fof(f269,plain,(
    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    inference(backward_demodulation,[],[f124,f262])).

fof(f262,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f259,f64])).

fof(f64,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f259,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f94,f60])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f124,plain,(
    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(resolution,[],[f74,f116])).

fof(f116,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f113,f86])).

fof(f86,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f113,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f79,f60])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f341,plain,(
    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f303,f109])).

fof(f109,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f303,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | k9_relat_1(sK2,k10_relat_1(sK2,X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f302,f116])).

fof(f302,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | k9_relat_1(sK2,k10_relat_1(sK2,X3)) = X3
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f291,f58])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f291,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | k9_relat_1(sK2,k10_relat_1(sK2,X3)) = X3
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f90,f262])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f1042,plain,(
    k1_relat_1(sK3) = k9_relat_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f734,f999])).

fof(f999,plain,(
    sK0 = k10_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f996,f104])).

fof(f104,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f72,f70])).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f72,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f996,plain,(
    k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f422,f991])).

fof(f991,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f980,f990])).

fof(f990,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f974,f327])).

fof(f327,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f97,f102])).

fof(f102,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f71,f70])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f974,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f65,f819])).

fof(f819,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f816,f58])).

fof(f816,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f340,f60])).

fof(f340,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f337,f61])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f337,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f99,f63])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f99,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f65,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f980,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f979,f58])).

fof(f979,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f978,f60])).

fof(f978,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f977,f61])).

fof(f977,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f975,f63])).

fof(f975,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f101,f819])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f422,plain,(
    k1_relat_1(k5_relat_1(sK2,sK3)) = k10_relat_1(sK2,k1_relat_1(sK3)) ),
    inference(resolution,[],[f254,f116])).

fof(f254,plain,(
    ! [X9] :
      ( ~ v1_relat_1(X9)
      | k1_relat_1(k5_relat_1(X9,sK3)) = k10_relat_1(X9,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f77,f117])).

fof(f117,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f114,f86])).

fof(f114,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f79,f63])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f734,plain,(
    k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) ),
    inference(subsumption_resolution,[],[f721,f117])).

fof(f721,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3)))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f344,f187])).

fof(f187,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f95,f63])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f344,plain,(
    ! [X2] :
      ( ~ v4_relat_1(X2,sK1)
      | k1_relat_1(X2) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X2)))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f303,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f203,plain,(
    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f106,f117])).

fof(f106,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f76,f70])).

fof(f76,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1713,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f1708,f280])).

fof(f280,plain,(
    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f279,f262])).

fof(f279,plain,(
    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f278,f116])).

fof(f278,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f277,f58])).

fof(f277,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f107,f66])).

fof(f66,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f85,f70])).

fof(f85,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f1708,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f1561,f218])).

fof(f218,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl4_7
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f1561,plain,(
    ! [X18] :
      ( ~ v1_relat_1(X18)
      | k5_relat_1(k5_relat_1(X18,sK2),sK3) = k5_relat_1(X18,k6_partfun1(sK0)) ) ),
    inference(forward_demodulation,[],[f1559,f991])).

fof(f1559,plain,(
    ! [X18] :
      ( k5_relat_1(k5_relat_1(X18,sK2),sK3) = k5_relat_1(X18,k5_relat_1(sK2,sK3))
      | ~ v1_relat_1(X18) ) ),
    inference(resolution,[],[f313,f116])).

fof(f313,plain,(
    ! [X14,X15] :
      ( ~ v1_relat_1(X15)
      | k5_relat_1(k5_relat_1(X14,X15),sK3) = k5_relat_1(X14,k5_relat_1(X15,sK3))
      | ~ v1_relat_1(X14) ) ),
    inference(resolution,[],[f78,f117])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f1094,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_7
    | ~ spl4_61 ),
    inference(backward_demodulation,[],[f355,f1060])).

fof(f355,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2)))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f245,f239])).

fof(f239,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f238,f116])).

fof(f238,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f237,f58])).

fof(f237,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f83,f66])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f245,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2))))
    | ~ spl4_7 ),
    inference(resolution,[],[f218,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f75,f70])).

fof(f75,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f1085,plain,(
    spl4_62 ),
    inference(avatar_contradiction_clause,[],[f1084])).

fof(f1084,plain,
    ( $false
    | spl4_62 ),
    inference(subsumption_resolution,[],[f1083,f116])).

fof(f1083,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_62 ),
    inference(subsumption_resolution,[],[f1082,f186])).

fof(f186,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f95,f60])).

fof(f1082,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | spl4_62 ),
    inference(resolution,[],[f1064,f88])).

fof(f1064,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_62 ),
    inference(avatar_component_clause,[],[f1062])).

fof(f1062,plain,
    ( spl4_62
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f1065,plain,
    ( spl4_61
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f1056,f1062,f1058])).

fof(f1056,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | sK0 = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f1045,f116])).

fof(f1045,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | sK0 = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f153,f999])).

fof(f153,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2))
      | k1_relat_1(X1) = k10_relat_1(X1,X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f93,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f243,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f241,f116])).

fof(f241,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_7 ),
    inference(subsumption_resolution,[],[f240,f58])).

fof(f240,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_7 ),
    inference(resolution,[],[f219,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f219,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:39:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (18089)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (18101)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (18109)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (18087)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (18092)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (18088)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (18098)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (18090)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (18093)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (18114)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (18108)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (18102)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (18091)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (18095)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (18118)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (18116)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (18104)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (18110)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (18106)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (18105)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (18103)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (18117)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (18094)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (18100)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (18103)Refutation not found, incomplete strategy% (18103)------------------------------
% 0.22/0.55  % (18103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18103)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18103)Memory used [KB]: 10746
% 0.22/0.55  % (18103)Time elapsed: 0.140 s
% 0.22/0.55  % (18103)------------------------------
% 0.22/0.55  % (18103)------------------------------
% 0.22/0.55  % (18096)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (18112)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (18097)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (18107)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (18115)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (18099)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.82/0.62  % (18093)Refutation found. Thanks to Tanya!
% 1.82/0.62  % SZS status Theorem for theBenchmark
% 1.82/0.62  % SZS output start Proof for theBenchmark
% 1.82/0.62  fof(f1720,plain,(
% 1.82/0.62    $false),
% 1.82/0.62    inference(avatar_sat_refutation,[],[f243,f1065,f1085,f1718])).
% 1.82/0.63  fof(f1718,plain,(
% 1.82/0.63    ~spl4_7 | ~spl4_61),
% 1.82/0.63    inference(avatar_contradiction_clause,[],[f1717])).
% 1.82/0.63  fof(f1717,plain,(
% 1.82/0.63    $false | (~spl4_7 | ~spl4_61)),
% 1.82/0.63    inference(subsumption_resolution,[],[f1715,f69])).
% 1.82/0.63  fof(f69,plain,(
% 1.82/0.63    k2_funct_1(sK2) != sK3),
% 1.82/0.63    inference(cnf_transformation,[],[f53])).
% 1.82/0.63  fof(f53,plain,(
% 1.82/0.63    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.82/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f52,f51])).
% 1.82/0.63  fof(f51,plain,(
% 1.82/0.63    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.82/0.63    introduced(choice_axiom,[])).
% 1.82/0.63  fof(f52,plain,(
% 1.82/0.63    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.82/0.63    introduced(choice_axiom,[])).
% 1.82/0.63  fof(f26,plain,(
% 1.82/0.63    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.82/0.63    inference(flattening,[],[f25])).
% 1.82/0.63  fof(f25,plain,(
% 1.82/0.63    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.82/0.63    inference(ennf_transformation,[],[f24])).
% 1.82/0.63  fof(f24,negated_conjecture,(
% 1.82/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.82/0.63    inference(negated_conjecture,[],[f23])).
% 1.82/0.63  fof(f23,conjecture,(
% 1.82/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.82/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.82/0.63  fof(f1715,plain,(
% 1.82/0.63    k2_funct_1(sK2) = sK3 | (~spl4_7 | ~spl4_61)),
% 1.82/0.63    inference(backward_demodulation,[],[f1094,f1714])).
% 1.82/0.63  fof(f1714,plain,(
% 1.82/0.63    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | (~spl4_7 | ~spl4_61)),
% 1.82/0.63    inference(forward_demodulation,[],[f1713,f1168])).
% 1.82/0.63  fof(f1168,plain,(
% 1.82/0.63    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_61),
% 1.82/0.63    inference(backward_demodulation,[],[f203,f1166])).
% 1.82/0.63  fof(f1166,plain,(
% 1.82/0.63    sK1 = k1_relat_1(sK3) | ~spl4_61),
% 1.82/0.63    inference(forward_demodulation,[],[f1042,f1093])).
% 1.82/0.63  fof(f1093,plain,(
% 1.82/0.63    sK1 = k9_relat_1(sK2,sK0) | ~spl4_61),
% 1.82/0.63    inference(backward_demodulation,[],[f345,f1060])).
% 1.82/0.63  fof(f1060,plain,(
% 1.82/0.63    sK0 = k1_relat_1(sK2) | ~spl4_61),
% 1.82/0.63    inference(avatar_component_clause,[],[f1058])).
% 1.82/0.63  fof(f1058,plain,(
% 1.82/0.63    spl4_61 <=> sK0 = k1_relat_1(sK2)),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 1.82/0.63  fof(f345,plain,(
% 1.82/0.63    sK1 = k9_relat_1(sK2,k1_relat_1(sK2))),
% 1.82/0.63    inference(forward_demodulation,[],[f341,f269])).
% 1.82/0.63  fof(f269,plain,(
% 1.82/0.63    k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 1.82/0.63    inference(backward_demodulation,[],[f124,f262])).
% 1.82/0.63  fof(f262,plain,(
% 1.82/0.63    sK1 = k2_relat_1(sK2)),
% 1.82/0.63    inference(forward_demodulation,[],[f259,f64])).
% 1.82/0.63  fof(f64,plain,(
% 1.82/0.63    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.82/0.63    inference(cnf_transformation,[],[f53])).
% 1.82/0.63  fof(f259,plain,(
% 1.82/0.63    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.82/0.63    inference(resolution,[],[f94,f60])).
% 1.82/0.63  fof(f60,plain,(
% 1.82/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.82/0.63    inference(cnf_transformation,[],[f53])).
% 1.82/0.63  fof(f94,plain,(
% 1.82/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f43])).
% 1.82/0.63  fof(f43,plain,(
% 1.82/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.82/0.63    inference(ennf_transformation,[],[f17])).
% 1.82/0.63  fof(f17,axiom,(
% 1.82/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.82/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.82/0.63  fof(f124,plain,(
% 1.82/0.63    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)),
% 1.82/0.63    inference(resolution,[],[f74,f116])).
% 1.82/0.63  fof(f116,plain,(
% 1.82/0.63    v1_relat_1(sK2)),
% 1.82/0.63    inference(subsumption_resolution,[],[f113,f86])).
% 1.82/0.63  fof(f86,plain,(
% 1.82/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.82/0.63    inference(cnf_transformation,[],[f4])).
% 1.82/0.63  fof(f4,axiom,(
% 1.82/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.82/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.82/0.63  fof(f113,plain,(
% 1.82/0.63    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.82/0.63    inference(resolution,[],[f79,f60])).
% 1.82/0.63  fof(f79,plain,(
% 1.82/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f32])).
% 1.82/0.63  fof(f32,plain,(
% 1.82/0.63    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.82/0.63    inference(ennf_transformation,[],[f2])).
% 1.82/0.63  fof(f2,axiom,(
% 1.82/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.82/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.82/0.63  fof(f74,plain,(
% 1.82/0.63    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f27])).
% 1.82/0.63  fof(f27,plain,(
% 1.82/0.63    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.82/0.63    inference(ennf_transformation,[],[f6])).
% 1.82/0.63  fof(f6,axiom,(
% 1.82/0.63    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.82/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.82/0.63  fof(f341,plain,(
% 1.82/0.63    sK1 = k9_relat_1(sK2,k10_relat_1(sK2,sK1))),
% 1.82/0.63    inference(resolution,[],[f303,f109])).
% 1.82/0.63  fof(f109,plain,(
% 1.82/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.82/0.63    inference(equality_resolution,[],[f92])).
% 1.82/0.63  fof(f92,plain,(
% 1.82/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.82/0.63    inference(cnf_transformation,[],[f56])).
% 1.82/0.63  fof(f56,plain,(
% 1.82/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.82/0.63    inference(flattening,[],[f55])).
% 1.82/0.63  fof(f55,plain,(
% 1.82/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.82/0.63    inference(nnf_transformation,[],[f1])).
% 1.82/0.63  fof(f1,axiom,(
% 1.82/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.82/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.82/0.63  fof(f303,plain,(
% 1.82/0.63    ( ! [X3] : (~r1_tarski(X3,sK1) | k9_relat_1(sK2,k10_relat_1(sK2,X3)) = X3) )),
% 1.82/0.63    inference(subsumption_resolution,[],[f302,f116])).
% 1.82/0.63  fof(f302,plain,(
% 1.82/0.63    ( ! [X3] : (~r1_tarski(X3,sK1) | k9_relat_1(sK2,k10_relat_1(sK2,X3)) = X3 | ~v1_relat_1(sK2)) )),
% 1.82/0.63    inference(subsumption_resolution,[],[f291,f58])).
% 1.82/0.63  fof(f58,plain,(
% 1.82/0.63    v1_funct_1(sK2)),
% 1.82/0.63    inference(cnf_transformation,[],[f53])).
% 1.82/0.63  fof(f291,plain,(
% 1.82/0.63    ( ! [X3] : (~r1_tarski(X3,sK1) | k9_relat_1(sK2,k10_relat_1(sK2,X3)) = X3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.82/0.63    inference(superposition,[],[f90,f262])).
% 1.82/0.63  fof(f90,plain,(
% 1.82/0.63    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f42])).
% 1.82/0.63  fof(f42,plain,(
% 1.82/0.63    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.82/0.63    inference(flattening,[],[f41])).
% 1.82/0.63  fof(f41,plain,(
% 1.82/0.63    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.82/0.63    inference(ennf_transformation,[],[f13])).
% 1.82/0.63  fof(f13,axiom,(
% 1.82/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.82/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.82/0.63  fof(f1042,plain,(
% 1.82/0.63    k1_relat_1(sK3) = k9_relat_1(sK2,sK0)),
% 1.82/0.63    inference(backward_demodulation,[],[f734,f999])).
% 1.82/0.63  fof(f999,plain,(
% 1.82/0.63    sK0 = k10_relat_1(sK2,k1_relat_1(sK3))),
% 1.82/0.63    inference(forward_demodulation,[],[f996,f104])).
% 1.82/0.63  fof(f104,plain,(
% 1.82/0.63    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.82/0.63    inference(definition_unfolding,[],[f72,f70])).
% 1.82/0.63  fof(f70,plain,(
% 1.82/0.63    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f22])).
% 1.82/0.63  fof(f22,axiom,(
% 1.82/0.63    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.82/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.82/0.63  fof(f72,plain,(
% 1.82/0.63    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.82/0.63    inference(cnf_transformation,[],[f9])).
% 1.82/0.63  fof(f9,axiom,(
% 1.82/0.63    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.82/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.82/0.63  fof(f996,plain,(
% 1.82/0.63    k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k6_partfun1(sK0))),
% 1.82/0.63    inference(backward_demodulation,[],[f422,f991])).
% 1.82/0.63  fof(f991,plain,(
% 1.82/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.82/0.63    inference(global_subsumption,[],[f980,f990])).
% 1.82/0.63  fof(f990,plain,(
% 1.82/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.82/0.63    inference(resolution,[],[f974,f327])).
% 1.82/0.63  fof(f327,plain,(
% 1.82/0.63    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.82/0.63    inference(resolution,[],[f97,f102])).
% 1.82/0.63  fof(f102,plain,(
% 1.82/0.63    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.82/0.63    inference(definition_unfolding,[],[f71,f70])).
% 1.82/0.63  fof(f71,plain,(
% 1.82/0.63    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.82/0.63    inference(cnf_transformation,[],[f19])).
% 2.05/0.63  fof(f19,axiom,(
% 2.05/0.63    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 2.05/0.63  fof(f97,plain,(
% 2.05/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f57])).
% 2.05/0.63  fof(f57,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.05/0.63    inference(nnf_transformation,[],[f46])).
% 2.05/0.63  fof(f46,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.05/0.63    inference(flattening,[],[f45])).
% 2.05/0.63  fof(f45,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.05/0.63    inference(ennf_transformation,[],[f18])).
% 2.05/0.63  fof(f18,axiom,(
% 2.05/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.05/0.63  fof(f974,plain,(
% 2.05/0.63    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.05/0.63    inference(backward_demodulation,[],[f65,f819])).
% 2.05/0.63  fof(f819,plain,(
% 2.05/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.05/0.63    inference(subsumption_resolution,[],[f816,f58])).
% 2.05/0.63  fof(f816,plain,(
% 2.05/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 2.05/0.63    inference(resolution,[],[f340,f60])).
% 2.05/0.63  fof(f340,plain,(
% 2.05/0.63    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 2.05/0.63    inference(subsumption_resolution,[],[f337,f61])).
% 2.05/0.63  fof(f61,plain,(
% 2.05/0.63    v1_funct_1(sK3)),
% 2.05/0.63    inference(cnf_transformation,[],[f53])).
% 2.05/0.63  fof(f337,plain,(
% 2.05/0.63    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 2.05/0.63    inference(resolution,[],[f99,f63])).
% 2.05/0.63  fof(f63,plain,(
% 2.05/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.05/0.63    inference(cnf_transformation,[],[f53])).
% 2.05/0.63  fof(f99,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f48])).
% 2.05/0.63  fof(f48,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.05/0.63    inference(flattening,[],[f47])).
% 2.05/0.63  fof(f47,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.05/0.63    inference(ennf_transformation,[],[f21])).
% 2.05/0.63  fof(f21,axiom,(
% 2.05/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.05/0.63  fof(f65,plain,(
% 2.05/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.05/0.63    inference(cnf_transformation,[],[f53])).
% 2.05/0.63  fof(f980,plain,(
% 2.05/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.05/0.63    inference(subsumption_resolution,[],[f979,f58])).
% 2.05/0.63  fof(f979,plain,(
% 2.05/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 2.05/0.63    inference(subsumption_resolution,[],[f978,f60])).
% 2.05/0.63  fof(f978,plain,(
% 2.05/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.05/0.63    inference(subsumption_resolution,[],[f977,f61])).
% 2.05/0.63  fof(f977,plain,(
% 2.05/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.05/0.63    inference(subsumption_resolution,[],[f975,f63])).
% 2.05/0.63  fof(f975,plain,(
% 2.05/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.05/0.63    inference(superposition,[],[f101,f819])).
% 2.05/0.63  fof(f101,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f50])).
% 2.05/0.63  fof(f50,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.05/0.63    inference(flattening,[],[f49])).
% 2.05/0.63  fof(f49,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.05/0.63    inference(ennf_transformation,[],[f20])).
% 2.05/0.63  fof(f20,axiom,(
% 2.05/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.05/0.63  fof(f422,plain,(
% 2.05/0.63    k1_relat_1(k5_relat_1(sK2,sK3)) = k10_relat_1(sK2,k1_relat_1(sK3))),
% 2.05/0.63    inference(resolution,[],[f254,f116])).
% 2.05/0.63  fof(f254,plain,(
% 2.05/0.63    ( ! [X9] : (~v1_relat_1(X9) | k1_relat_1(k5_relat_1(X9,sK3)) = k10_relat_1(X9,k1_relat_1(sK3))) )),
% 2.05/0.63    inference(resolution,[],[f77,f117])).
% 2.05/0.63  fof(f117,plain,(
% 2.05/0.63    v1_relat_1(sK3)),
% 2.05/0.63    inference(subsumption_resolution,[],[f114,f86])).
% 2.05/0.63  fof(f114,plain,(
% 2.05/0.63    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.05/0.63    inference(resolution,[],[f79,f63])).
% 2.05/0.63  fof(f77,plain,(
% 2.05/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f30])).
% 2.05/0.63  fof(f30,plain,(
% 2.05/0.63    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.05/0.63    inference(ennf_transformation,[],[f7])).
% 2.05/0.63  fof(f7,axiom,(
% 2.05/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 2.05/0.63  fof(f734,plain,(
% 2.05/0.63    k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3)))),
% 2.05/0.63    inference(subsumption_resolution,[],[f721,f117])).
% 2.05/0.63  fof(f721,plain,(
% 2.05/0.63    k1_relat_1(sK3) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) | ~v1_relat_1(sK3)),
% 2.05/0.63    inference(resolution,[],[f344,f187])).
% 2.05/0.63  fof(f187,plain,(
% 2.05/0.63    v4_relat_1(sK3,sK1)),
% 2.05/0.63    inference(resolution,[],[f95,f63])).
% 2.05/0.63  fof(f95,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f44])).
% 2.05/0.63  fof(f44,plain,(
% 2.05/0.63    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.05/0.63    inference(ennf_transformation,[],[f16])).
% 2.05/0.63  fof(f16,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.05/0.63  fof(f344,plain,(
% 2.05/0.63    ( ! [X2] : (~v4_relat_1(X2,sK1) | k1_relat_1(X2) = k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(X2))) | ~v1_relat_1(X2)) )),
% 2.05/0.63    inference(resolution,[],[f303,f88])).
% 2.05/0.63  fof(f88,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f54])).
% 2.05/0.63  fof(f54,plain,(
% 2.05/0.63    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.05/0.63    inference(nnf_transformation,[],[f40])).
% 2.05/0.63  fof(f40,plain,(
% 2.05/0.63    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.05/0.63    inference(ennf_transformation,[],[f3])).
% 2.05/0.63  fof(f3,axiom,(
% 2.05/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.05/0.63  fof(f203,plain,(
% 2.05/0.63    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)),
% 2.05/0.63    inference(resolution,[],[f106,f117])).
% 2.05/0.63  fof(f106,plain,(
% 2.05/0.63    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 2.05/0.63    inference(definition_unfolding,[],[f76,f70])).
% 2.05/0.63  fof(f76,plain,(
% 2.05/0.63    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f29])).
% 2.05/0.63  fof(f29,plain,(
% 2.05/0.63    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.05/0.63    inference(ennf_transformation,[],[f10])).
% 2.05/0.63  fof(f10,axiom,(
% 2.05/0.63    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 2.05/0.63  fof(f1713,plain,(
% 2.05/0.63    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_7),
% 2.05/0.63    inference(forward_demodulation,[],[f1708,f280])).
% 2.05/0.63  fof(f280,plain,(
% 2.05/0.63    k6_partfun1(sK1) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 2.05/0.63    inference(forward_demodulation,[],[f279,f262])).
% 2.05/0.63  fof(f279,plain,(
% 2.05/0.63    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 2.05/0.63    inference(subsumption_resolution,[],[f278,f116])).
% 2.05/0.63  fof(f278,plain,(
% 2.05/0.63    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_relat_1(sK2)),
% 2.05/0.63    inference(subsumption_resolution,[],[f277,f58])).
% 2.05/0.63  fof(f277,plain,(
% 2.05/0.63    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.05/0.63    inference(resolution,[],[f107,f66])).
% 2.05/0.63  fof(f66,plain,(
% 2.05/0.63    v2_funct_1(sK2)),
% 2.05/0.63    inference(cnf_transformation,[],[f53])).
% 2.05/0.63  fof(f107,plain,(
% 2.05/0.63    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f85,f70])).
% 2.05/0.63  fof(f85,plain,(
% 2.05/0.63    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f38])).
% 2.05/0.63  fof(f38,plain,(
% 2.05/0.63    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.05/0.63    inference(flattening,[],[f37])).
% 2.05/0.63  fof(f37,plain,(
% 2.05/0.63    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.05/0.63    inference(ennf_transformation,[],[f15])).
% 2.05/0.63  fof(f15,axiom,(
% 2.05/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 2.05/0.63  fof(f1708,plain,(
% 2.05/0.63    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),sK3) | ~spl4_7),
% 2.05/0.63    inference(resolution,[],[f1561,f218])).
% 2.05/0.63  fof(f218,plain,(
% 2.05/0.63    v1_relat_1(k2_funct_1(sK2)) | ~spl4_7),
% 2.05/0.63    inference(avatar_component_clause,[],[f217])).
% 2.05/0.63  fof(f217,plain,(
% 2.05/0.63    spl4_7 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.05/0.63  fof(f1561,plain,(
% 2.05/0.63    ( ! [X18] : (~v1_relat_1(X18) | k5_relat_1(k5_relat_1(X18,sK2),sK3) = k5_relat_1(X18,k6_partfun1(sK0))) )),
% 2.05/0.63    inference(forward_demodulation,[],[f1559,f991])).
% 2.05/0.63  fof(f1559,plain,(
% 2.05/0.63    ( ! [X18] : (k5_relat_1(k5_relat_1(X18,sK2),sK3) = k5_relat_1(X18,k5_relat_1(sK2,sK3)) | ~v1_relat_1(X18)) )),
% 2.05/0.63    inference(resolution,[],[f313,f116])).
% 2.05/0.63  fof(f313,plain,(
% 2.05/0.63    ( ! [X14,X15] : (~v1_relat_1(X15) | k5_relat_1(k5_relat_1(X14,X15),sK3) = k5_relat_1(X14,k5_relat_1(X15,sK3)) | ~v1_relat_1(X14)) )),
% 2.05/0.63    inference(resolution,[],[f78,f117])).
% 2.05/0.63  fof(f78,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f31])).
% 2.05/0.63  fof(f31,plain,(
% 2.05/0.63    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.05/0.63    inference(ennf_transformation,[],[f8])).
% 2.05/0.63  fof(f8,axiom,(
% 2.05/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 2.05/0.63  fof(f1094,plain,(
% 2.05/0.63    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | (~spl4_7 | ~spl4_61)),
% 2.05/0.63    inference(backward_demodulation,[],[f355,f1060])).
% 2.05/0.63  fof(f355,plain,(
% 2.05/0.63    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) | ~spl4_7),
% 2.05/0.63    inference(forward_demodulation,[],[f245,f239])).
% 2.05/0.63  fof(f239,plain,(
% 2.05/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 2.05/0.63    inference(subsumption_resolution,[],[f238,f116])).
% 2.05/0.63  fof(f238,plain,(
% 2.05/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.05/0.63    inference(subsumption_resolution,[],[f237,f58])).
% 2.05/0.63  fof(f237,plain,(
% 2.05/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.05/0.63    inference(resolution,[],[f83,f66])).
% 2.05/0.63  fof(f83,plain,(
% 2.05/0.63    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f36])).
% 2.05/0.63  fof(f36,plain,(
% 2.05/0.63    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.05/0.63    inference(flattening,[],[f35])).
% 2.05/0.63  fof(f35,plain,(
% 2.05/0.63    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.05/0.63    inference(ennf_transformation,[],[f14])).
% 2.05/0.63  fof(f14,axiom,(
% 2.05/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 2.05/0.63  fof(f245,plain,(
% 2.05/0.63    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) | ~spl4_7),
% 2.05/0.63    inference(resolution,[],[f218,f105])).
% 2.05/0.63  fof(f105,plain,(
% 2.05/0.63    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 2.05/0.63    inference(definition_unfolding,[],[f75,f70])).
% 2.05/0.63  fof(f75,plain,(
% 2.05/0.63    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f28])).
% 2.05/0.63  fof(f28,plain,(
% 2.05/0.63    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.05/0.63    inference(ennf_transformation,[],[f11])).
% 2.05/0.63  fof(f11,axiom,(
% 2.05/0.63    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 2.05/0.63  fof(f1085,plain,(
% 2.05/0.63    spl4_62),
% 2.05/0.63    inference(avatar_contradiction_clause,[],[f1084])).
% 2.05/0.63  fof(f1084,plain,(
% 2.05/0.63    $false | spl4_62),
% 2.05/0.63    inference(subsumption_resolution,[],[f1083,f116])).
% 2.05/0.63  fof(f1083,plain,(
% 2.05/0.63    ~v1_relat_1(sK2) | spl4_62),
% 2.05/0.63    inference(subsumption_resolution,[],[f1082,f186])).
% 2.05/0.63  fof(f186,plain,(
% 2.05/0.63    v4_relat_1(sK2,sK0)),
% 2.05/0.63    inference(resolution,[],[f95,f60])).
% 2.05/0.63  fof(f1082,plain,(
% 2.05/0.63    ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | spl4_62),
% 2.05/0.63    inference(resolution,[],[f1064,f88])).
% 2.05/0.63  fof(f1064,plain,(
% 2.05/0.63    ~r1_tarski(k1_relat_1(sK2),sK0) | spl4_62),
% 2.05/0.63    inference(avatar_component_clause,[],[f1062])).
% 2.05/0.63  fof(f1062,plain,(
% 2.05/0.63    spl4_62 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 2.05/0.63  fof(f1065,plain,(
% 2.05/0.63    spl4_61 | ~spl4_62),
% 2.05/0.63    inference(avatar_split_clause,[],[f1056,f1062,f1058])).
% 2.05/0.63  fof(f1056,plain,(
% 2.05/0.63    ~r1_tarski(k1_relat_1(sK2),sK0) | sK0 = k1_relat_1(sK2)),
% 2.05/0.63    inference(subsumption_resolution,[],[f1045,f116])).
% 2.05/0.63  fof(f1045,plain,(
% 2.05/0.63    ~r1_tarski(k1_relat_1(sK2),sK0) | sK0 = k1_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.05/0.63    inference(superposition,[],[f153,f999])).
% 2.05/0.63  fof(f153,plain,(
% 2.05/0.63    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(X1),k10_relat_1(X1,X2)) | k1_relat_1(X1) = k10_relat_1(X1,X2) | ~v1_relat_1(X1)) )),
% 2.05/0.63    inference(resolution,[],[f93,f87])).
% 2.05/0.63  fof(f87,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f39])).
% 2.05/0.63  fof(f39,plain,(
% 2.05/0.63    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.05/0.63    inference(ennf_transformation,[],[f5])).
% 2.05/0.63  fof(f5,axiom,(
% 2.05/0.63    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.05/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 2.07/0.63  fof(f93,plain,(
% 2.07/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f56])).
% 2.07/0.63  fof(f243,plain,(
% 2.07/0.63    spl4_7),
% 2.07/0.63    inference(avatar_contradiction_clause,[],[f242])).
% 2.07/0.63  fof(f242,plain,(
% 2.07/0.63    $false | spl4_7),
% 2.07/0.63    inference(subsumption_resolution,[],[f241,f116])).
% 2.07/0.63  fof(f241,plain,(
% 2.07/0.63    ~v1_relat_1(sK2) | spl4_7),
% 2.07/0.63    inference(subsumption_resolution,[],[f240,f58])).
% 2.07/0.63  fof(f240,plain,(
% 2.07/0.63    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_7),
% 2.07/0.63    inference(resolution,[],[f219,f80])).
% 2.07/0.63  fof(f80,plain,(
% 2.07/0.63    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.63    inference(cnf_transformation,[],[f34])).
% 2.07/0.63  fof(f34,plain,(
% 2.07/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.07/0.63    inference(flattening,[],[f33])).
% 2.07/0.63  fof(f33,plain,(
% 2.07/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.07/0.63    inference(ennf_transformation,[],[f12])).
% 2.07/0.63  fof(f12,axiom,(
% 2.07/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.07/0.63  fof(f219,plain,(
% 2.07/0.63    ~v1_relat_1(k2_funct_1(sK2)) | spl4_7),
% 2.07/0.63    inference(avatar_component_clause,[],[f217])).
% 2.07/0.63  % SZS output end Proof for theBenchmark
% 2.07/0.63  % (18093)------------------------------
% 2.07/0.63  % (18093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.07/0.63  % (18093)Termination reason: Refutation
% 2.07/0.63  
% 2.07/0.63  % (18093)Memory used [KB]: 12281
% 2.07/0.63  % (18093)Time elapsed: 0.164 s
% 2.07/0.63  % (18093)------------------------------
% 2.07/0.63  % (18093)------------------------------
% 2.07/0.64  % (18083)Success in time 0.271 s
%------------------------------------------------------------------------------
