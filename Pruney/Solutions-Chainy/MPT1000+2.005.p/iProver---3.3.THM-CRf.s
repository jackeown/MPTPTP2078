%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:19 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :  121 (1478 expanded)
%              Number of clauses        :   72 ( 583 expanded)
%              Number of leaves         :   14 ( 264 expanded)
%              Depth                    :   26
%              Number of atoms          :  331 (5258 expanded)
%              Number of equality atoms :  190 (2639 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f24,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) != X0
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1) ) ),
    inference(flattening,[],[f42])).

fof(f58,plain,
    ( ? [X0,X1,X2] :
        ( k8_relset_1(X0,X1,X2,X1) != X0
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) )
   => ( k8_relset_1(sK3,sK4,sK5,sK4) != sK3
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 != sK4 )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( k8_relset_1(sK3,sK4,sK5,sK4) != sK3
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 != sK4 )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f43,f58])).

fof(f93,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f59])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f83,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f96,plain,(
    k8_relset_1(sK3,sK4,sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f59])).

fof(f95,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f59])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f103,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f88])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_515,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_35])).

cnf(c_516,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | k1_relset_1(X0,X1,sK5) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_684,plain,
    ( k1_relset_1(X0,X1,sK5) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK5 != sK5
    | sK4 != X1
    | sK3 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_516])).

cnf(c_685,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_1098,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_685])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_560,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_35])).

cnf(c_561,plain,
    ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_2357,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(equality_resolution,[status(thm)],[c_561])).

cnf(c_2465,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1098,c_2357])).

cnf(c_24,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_16,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_456,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_24,c_16])).

cnf(c_500,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_456,c_35])).

cnf(c_501,plain,
    ( r1_tarski(k2_relat_1(sK5),X0)
    | ~ v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_2149,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | r1_tarski(k2_relat_1(sK5),X1) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_502,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | r1_tarski(k2_relat_1(sK5),X1) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_1596,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2351,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1596])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_485,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_35])).

cnf(c_486,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_2346,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_2490,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK5)
    | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2346])).

cnf(c_2491,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2490])).

cnf(c_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2575,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2576,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2575])).

cnf(c_2624,plain,
    ( r1_tarski(k2_relat_1(sK5),X1) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2149,c_502,c_2351,c_2491,c_2576])).

cnf(c_2625,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | r1_tarski(k2_relat_1(sK5),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2624])).

cnf(c_2632,plain,
    ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2625])).

cnf(c_22,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2153,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3860,plain,
    ( k5_relat_1(sK5,k6_relat_1(sK4)) = sK5
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2632,c_2153])).

cnf(c_4190,plain,
    ( k5_relat_1(sK5,k6_relat_1(sK4)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3860,c_2351,c_2491,c_2576])).

cnf(c_23,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2152,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2150,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_2618,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2150,c_2351,c_2491,c_2576])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2154,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3957,plain,
    ( k10_relat_1(sK5,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK5,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2618,c_2154])).

cnf(c_4054,plain,
    ( k10_relat_1(sK5,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK5,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_2152,c_3957])).

cnf(c_21,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_4059,plain,
    ( k1_relat_1(k5_relat_1(sK5,k6_relat_1(X0))) = k10_relat_1(sK5,X0) ),
    inference(light_normalisation,[status(thm)],[c_4054,c_21])).

cnf(c_4282,plain,
    ( k10_relat_1(sK5,sK4) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4190,c_4059])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_551,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_35])).

cnf(c_552,plain,
    ( k8_relset_1(X0,X1,sK5,X2) = k10_relat_1(sK5,X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_2360,plain,
    ( k8_relset_1(sK3,sK4,sK5,X0) = k10_relat_1(sK5,X0) ),
    inference(equality_resolution,[status(thm)],[c_552])).

cnf(c_33,negated_conjecture,
    ( k8_relset_1(sK3,sK4,sK5,sK4) != sK3 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2442,plain,
    ( k10_relat_1(sK5,sK4) != sK3 ),
    inference(demodulation,[status(thm)],[c_2360,c_33])).

cnf(c_4333,plain,
    ( k1_relat_1(sK5) != sK3 ),
    inference(demodulation,[status(thm)],[c_4282,c_2442])).

cnf(c_4500,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2465,c_4333])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_4575,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4500,c_34])).

cnf(c_4576,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4575])).

cnf(c_4648,plain,
    ( k1_relat_1(sK5) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4576,c_4333])).

cnf(c_4570,plain,
    ( k1_relset_1(sK3,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
    inference(demodulation,[status(thm)],[c_4500,c_2357])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_604,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_35])).

cnf(c_605,plain,
    ( ~ v1_funct_2(sK5,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK5) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_709,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK5) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK5 != sK5
    | sK4 != X0
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_605])).

cnf(c_710,plain,
    ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_709])).

cnf(c_4572,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | sK3 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4500,c_710])).

cnf(c_4591,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4572,c_4576])).

cnf(c_4592,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4591])).

cnf(c_4596,plain,
    ( k1_relat_1(sK5) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4570,c_4576,c_4592])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4648,c_4596])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.97/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/0.98  
% 2.97/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.97/0.98  
% 2.97/0.98  ------  iProver source info
% 2.97/0.98  
% 2.97/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.97/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.97/0.98  git: non_committed_changes: false
% 2.97/0.98  git: last_make_outside_of_git: false
% 2.97/0.98  
% 2.97/0.98  ------ 
% 2.97/0.98  
% 2.97/0.98  ------ Input Options
% 2.97/0.98  
% 2.97/0.98  --out_options                           all
% 2.97/0.98  --tptp_safe_out                         true
% 2.97/0.98  --problem_path                          ""
% 2.97/0.98  --include_path                          ""
% 2.97/0.98  --clausifier                            res/vclausify_rel
% 2.97/0.98  --clausifier_options                    --mode clausify
% 2.97/0.98  --stdin                                 false
% 2.97/0.98  --stats_out                             all
% 2.97/0.98  
% 2.97/0.98  ------ General Options
% 2.97/0.98  
% 2.97/0.98  --fof                                   false
% 2.97/0.98  --time_out_real                         305.
% 2.97/0.98  --time_out_virtual                      -1.
% 2.97/0.98  --symbol_type_check                     false
% 2.97/0.98  --clausify_out                          false
% 2.97/0.98  --sig_cnt_out                           false
% 2.97/0.98  --trig_cnt_out                          false
% 2.97/0.98  --trig_cnt_out_tolerance                1.
% 2.97/0.98  --trig_cnt_out_sk_spl                   false
% 2.97/0.98  --abstr_cl_out                          false
% 2.97/0.98  
% 2.97/0.98  ------ Global Options
% 2.97/0.98  
% 2.97/0.98  --schedule                              default
% 2.97/0.98  --add_important_lit                     false
% 2.97/0.98  --prop_solver_per_cl                    1000
% 2.97/0.98  --min_unsat_core                        false
% 2.97/0.98  --soft_assumptions                      false
% 2.97/0.98  --soft_lemma_size                       3
% 2.97/0.98  --prop_impl_unit_size                   0
% 2.97/0.98  --prop_impl_unit                        []
% 2.97/0.98  --share_sel_clauses                     true
% 2.97/0.98  --reset_solvers                         false
% 2.97/0.98  --bc_imp_inh                            [conj_cone]
% 2.97/0.98  --conj_cone_tolerance                   3.
% 2.97/0.98  --extra_neg_conj                        none
% 2.97/0.98  --large_theory_mode                     true
% 2.97/0.98  --prolific_symb_bound                   200
% 2.97/0.98  --lt_threshold                          2000
% 2.97/0.98  --clause_weak_htbl                      true
% 2.97/0.98  --gc_record_bc_elim                     false
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing Options
% 2.97/0.98  
% 2.97/0.98  --preprocessing_flag                    true
% 2.97/0.98  --time_out_prep_mult                    0.1
% 2.97/0.98  --splitting_mode                        input
% 2.97/0.98  --splitting_grd                         true
% 2.97/0.98  --splitting_cvd                         false
% 2.97/0.98  --splitting_cvd_svl                     false
% 2.97/0.98  --splitting_nvd                         32
% 2.97/0.98  --sub_typing                            true
% 2.97/0.98  --prep_gs_sim                           true
% 2.97/0.98  --prep_unflatten                        true
% 2.97/0.98  --prep_res_sim                          true
% 2.97/0.98  --prep_upred                            true
% 2.97/0.98  --prep_sem_filter                       exhaustive
% 2.97/0.98  --prep_sem_filter_out                   false
% 2.97/0.98  --pred_elim                             true
% 2.97/0.98  --res_sim_input                         true
% 2.97/0.98  --eq_ax_congr_red                       true
% 2.97/0.98  --pure_diseq_elim                       true
% 2.97/0.98  --brand_transform                       false
% 2.97/0.98  --non_eq_to_eq                          false
% 2.97/0.98  --prep_def_merge                        true
% 2.97/0.98  --prep_def_merge_prop_impl              false
% 2.97/0.98  --prep_def_merge_mbd                    true
% 2.97/0.98  --prep_def_merge_tr_red                 false
% 2.97/0.98  --prep_def_merge_tr_cl                  false
% 2.97/0.98  --smt_preprocessing                     true
% 2.97/0.98  --smt_ac_axioms                         fast
% 2.97/0.98  --preprocessed_out                      false
% 2.97/0.98  --preprocessed_stats                    false
% 2.97/0.98  
% 2.97/0.98  ------ Abstraction refinement Options
% 2.97/0.98  
% 2.97/0.98  --abstr_ref                             []
% 2.97/0.98  --abstr_ref_prep                        false
% 2.97/0.98  --abstr_ref_until_sat                   false
% 2.97/0.98  --abstr_ref_sig_restrict                funpre
% 2.97/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.98  --abstr_ref_under                       []
% 2.97/0.98  
% 2.97/0.98  ------ SAT Options
% 2.97/0.98  
% 2.97/0.98  --sat_mode                              false
% 2.97/0.98  --sat_fm_restart_options                ""
% 2.97/0.98  --sat_gr_def                            false
% 2.97/0.98  --sat_epr_types                         true
% 2.97/0.98  --sat_non_cyclic_types                  false
% 2.97/0.98  --sat_finite_models                     false
% 2.97/0.98  --sat_fm_lemmas                         false
% 2.97/0.98  --sat_fm_prep                           false
% 2.97/0.98  --sat_fm_uc_incr                        true
% 2.97/0.98  --sat_out_model                         small
% 2.97/0.98  --sat_out_clauses                       false
% 2.97/0.98  
% 2.97/0.98  ------ QBF Options
% 2.97/0.98  
% 2.97/0.98  --qbf_mode                              false
% 2.97/0.98  --qbf_elim_univ                         false
% 2.97/0.98  --qbf_dom_inst                          none
% 2.97/0.98  --qbf_dom_pre_inst                      false
% 2.97/0.98  --qbf_sk_in                             false
% 2.97/0.98  --qbf_pred_elim                         true
% 2.97/0.98  --qbf_split                             512
% 2.97/0.98  
% 2.97/0.98  ------ BMC1 Options
% 2.97/0.98  
% 2.97/0.98  --bmc1_incremental                      false
% 2.97/0.98  --bmc1_axioms                           reachable_all
% 2.97/0.98  --bmc1_min_bound                        0
% 2.97/0.98  --bmc1_max_bound                        -1
% 2.97/0.98  --bmc1_max_bound_default                -1
% 2.97/0.98  --bmc1_symbol_reachability              true
% 2.97/0.98  --bmc1_property_lemmas                  false
% 2.97/0.98  --bmc1_k_induction                      false
% 2.97/0.98  --bmc1_non_equiv_states                 false
% 2.97/0.98  --bmc1_deadlock                         false
% 2.97/0.98  --bmc1_ucm                              false
% 2.97/0.98  --bmc1_add_unsat_core                   none
% 2.97/0.98  --bmc1_unsat_core_children              false
% 2.97/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.98  --bmc1_out_stat                         full
% 2.97/0.98  --bmc1_ground_init                      false
% 2.97/0.98  --bmc1_pre_inst_next_state              false
% 2.97/0.98  --bmc1_pre_inst_state                   false
% 2.97/0.98  --bmc1_pre_inst_reach_state             false
% 2.97/0.98  --bmc1_out_unsat_core                   false
% 2.97/0.98  --bmc1_aig_witness_out                  false
% 2.97/0.98  --bmc1_verbose                          false
% 2.97/0.98  --bmc1_dump_clauses_tptp                false
% 2.97/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.98  --bmc1_dump_file                        -
% 2.97/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.98  --bmc1_ucm_extend_mode                  1
% 2.97/0.98  --bmc1_ucm_init_mode                    2
% 2.97/0.98  --bmc1_ucm_cone_mode                    none
% 2.97/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.98  --bmc1_ucm_relax_model                  4
% 2.97/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.98  --bmc1_ucm_layered_model                none
% 2.97/0.98  --bmc1_ucm_max_lemma_size               10
% 2.97/0.98  
% 2.97/0.98  ------ AIG Options
% 2.97/0.98  
% 2.97/0.98  --aig_mode                              false
% 2.97/0.98  
% 2.97/0.98  ------ Instantiation Options
% 2.97/0.98  
% 2.97/0.98  --instantiation_flag                    true
% 2.97/0.98  --inst_sos_flag                         false
% 2.97/0.98  --inst_sos_phase                        true
% 2.97/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel_side                     num_symb
% 2.97/0.98  --inst_solver_per_active                1400
% 2.97/0.98  --inst_solver_calls_frac                1.
% 2.97/0.98  --inst_passive_queue_type               priority_queues
% 2.97/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.98  --inst_passive_queues_freq              [25;2]
% 2.97/0.98  --inst_dismatching                      true
% 2.97/0.98  --inst_eager_unprocessed_to_passive     true
% 2.97/0.98  --inst_prop_sim_given                   true
% 2.97/0.98  --inst_prop_sim_new                     false
% 2.97/0.98  --inst_subs_new                         false
% 2.97/0.98  --inst_eq_res_simp                      false
% 2.97/0.98  --inst_subs_given                       false
% 2.97/0.98  --inst_orphan_elimination               true
% 2.97/0.98  --inst_learning_loop_flag               true
% 2.97/0.98  --inst_learning_start                   3000
% 2.97/0.98  --inst_learning_factor                  2
% 2.97/0.98  --inst_start_prop_sim_after_learn       3
% 2.97/0.98  --inst_sel_renew                        solver
% 2.97/0.98  --inst_lit_activity_flag                true
% 2.97/0.98  --inst_restr_to_given                   false
% 2.97/0.98  --inst_activity_threshold               500
% 2.97/0.98  --inst_out_proof                        true
% 2.97/0.98  
% 2.97/0.98  ------ Resolution Options
% 2.97/0.98  
% 2.97/0.98  --resolution_flag                       true
% 2.97/0.98  --res_lit_sel                           adaptive
% 2.97/0.98  --res_lit_sel_side                      none
% 2.97/0.98  --res_ordering                          kbo
% 2.97/0.98  --res_to_prop_solver                    active
% 2.97/0.98  --res_prop_simpl_new                    false
% 2.97/0.98  --res_prop_simpl_given                  true
% 2.97/0.98  --res_passive_queue_type                priority_queues
% 2.97/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.98  --res_passive_queues_freq               [15;5]
% 2.97/0.98  --res_forward_subs                      full
% 2.97/0.98  --res_backward_subs                     full
% 2.97/0.98  --res_forward_subs_resolution           true
% 2.97/0.98  --res_backward_subs_resolution          true
% 2.97/0.98  --res_orphan_elimination                true
% 2.97/0.98  --res_time_limit                        2.
% 2.97/0.98  --res_out_proof                         true
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Options
% 2.97/0.98  
% 2.97/0.98  --superposition_flag                    true
% 2.97/0.98  --sup_passive_queue_type                priority_queues
% 2.97/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.98  --demod_completeness_check              fast
% 2.97/0.98  --demod_use_ground                      true
% 2.97/0.98  --sup_to_prop_solver                    passive
% 2.97/0.98  --sup_prop_simpl_new                    true
% 2.97/0.98  --sup_prop_simpl_given                  true
% 2.97/0.98  --sup_fun_splitting                     false
% 2.97/0.98  --sup_smt_interval                      50000
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Simplification Setup
% 2.97/0.98  
% 2.97/0.98  --sup_indices_passive                   []
% 2.97/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_full_bw                           [BwDemod]
% 2.97/0.98  --sup_immed_triv                        [TrivRules]
% 2.97/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_immed_bw_main                     []
% 2.97/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  
% 2.97/0.98  ------ Combination Options
% 2.97/0.98  
% 2.97/0.98  --comb_res_mult                         3
% 2.97/0.98  --comb_sup_mult                         2
% 2.97/0.98  --comb_inst_mult                        10
% 2.97/0.98  
% 2.97/0.98  ------ Debug Options
% 2.97/0.98  
% 2.97/0.98  --dbg_backtrace                         false
% 2.97/0.98  --dbg_dump_prop_clauses                 false
% 2.97/0.98  --dbg_dump_prop_clauses_file            -
% 2.97/0.98  --dbg_out_stat                          false
% 2.97/0.98  ------ Parsing...
% 2.97/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.97/0.98  ------ Proving...
% 2.97/0.98  ------ Problem Properties 
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  clauses                                 30
% 2.97/0.98  conjectures                             2
% 2.97/0.98  EPR                                     5
% 2.97/0.98  Horn                                    25
% 2.97/0.98  unary                                   8
% 2.97/0.98  binary                                  13
% 2.97/0.98  lits                                    62
% 2.97/0.98  lits eq                                 25
% 2.97/0.98  fd_pure                                 0
% 2.97/0.98  fd_pseudo                               0
% 2.97/0.98  fd_cond                                 1
% 2.97/0.98  fd_pseudo_cond                          2
% 2.97/0.98  AC symbols                              0
% 2.97/0.98  
% 2.97/0.98  ------ Schedule dynamic 5 is on 
% 2.97/0.98  
% 2.97/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  ------ 
% 2.97/0.98  Current options:
% 2.97/0.98  ------ 
% 2.97/0.98  
% 2.97/0.98  ------ Input Options
% 2.97/0.98  
% 2.97/0.98  --out_options                           all
% 2.97/0.98  --tptp_safe_out                         true
% 2.97/0.98  --problem_path                          ""
% 2.97/0.98  --include_path                          ""
% 2.97/0.98  --clausifier                            res/vclausify_rel
% 2.97/0.98  --clausifier_options                    --mode clausify
% 2.97/0.98  --stdin                                 false
% 2.97/0.98  --stats_out                             all
% 2.97/0.98  
% 2.97/0.98  ------ General Options
% 2.97/0.98  
% 2.97/0.98  --fof                                   false
% 2.97/0.98  --time_out_real                         305.
% 2.97/0.98  --time_out_virtual                      -1.
% 2.97/0.98  --symbol_type_check                     false
% 2.97/0.98  --clausify_out                          false
% 2.97/0.98  --sig_cnt_out                           false
% 2.97/0.98  --trig_cnt_out                          false
% 2.97/0.98  --trig_cnt_out_tolerance                1.
% 2.97/0.98  --trig_cnt_out_sk_spl                   false
% 2.97/0.98  --abstr_cl_out                          false
% 2.97/0.98  
% 2.97/0.98  ------ Global Options
% 2.97/0.98  
% 2.97/0.98  --schedule                              default
% 2.97/0.98  --add_important_lit                     false
% 2.97/0.98  --prop_solver_per_cl                    1000
% 2.97/0.98  --min_unsat_core                        false
% 2.97/0.98  --soft_assumptions                      false
% 2.97/0.98  --soft_lemma_size                       3
% 2.97/0.98  --prop_impl_unit_size                   0
% 2.97/0.98  --prop_impl_unit                        []
% 2.97/0.98  --share_sel_clauses                     true
% 2.97/0.98  --reset_solvers                         false
% 2.97/0.98  --bc_imp_inh                            [conj_cone]
% 2.97/0.98  --conj_cone_tolerance                   3.
% 2.97/0.98  --extra_neg_conj                        none
% 2.97/0.98  --large_theory_mode                     true
% 2.97/0.98  --prolific_symb_bound                   200
% 2.97/0.98  --lt_threshold                          2000
% 2.97/0.98  --clause_weak_htbl                      true
% 2.97/0.98  --gc_record_bc_elim                     false
% 2.97/0.98  
% 2.97/0.98  ------ Preprocessing Options
% 2.97/0.98  
% 2.97/0.98  --preprocessing_flag                    true
% 2.97/0.98  --time_out_prep_mult                    0.1
% 2.97/0.98  --splitting_mode                        input
% 2.97/0.98  --splitting_grd                         true
% 2.97/0.98  --splitting_cvd                         false
% 2.97/0.98  --splitting_cvd_svl                     false
% 2.97/0.98  --splitting_nvd                         32
% 2.97/0.98  --sub_typing                            true
% 2.97/0.98  --prep_gs_sim                           true
% 2.97/0.98  --prep_unflatten                        true
% 2.97/0.98  --prep_res_sim                          true
% 2.97/0.98  --prep_upred                            true
% 2.97/0.98  --prep_sem_filter                       exhaustive
% 2.97/0.98  --prep_sem_filter_out                   false
% 2.97/0.98  --pred_elim                             true
% 2.97/0.98  --res_sim_input                         true
% 2.97/0.98  --eq_ax_congr_red                       true
% 2.97/0.98  --pure_diseq_elim                       true
% 2.97/0.98  --brand_transform                       false
% 2.97/0.98  --non_eq_to_eq                          false
% 2.97/0.98  --prep_def_merge                        true
% 2.97/0.98  --prep_def_merge_prop_impl              false
% 2.97/0.98  --prep_def_merge_mbd                    true
% 2.97/0.98  --prep_def_merge_tr_red                 false
% 2.97/0.98  --prep_def_merge_tr_cl                  false
% 2.97/0.98  --smt_preprocessing                     true
% 2.97/0.98  --smt_ac_axioms                         fast
% 2.97/0.98  --preprocessed_out                      false
% 2.97/0.98  --preprocessed_stats                    false
% 2.97/0.98  
% 2.97/0.98  ------ Abstraction refinement Options
% 2.97/0.98  
% 2.97/0.98  --abstr_ref                             []
% 2.97/0.98  --abstr_ref_prep                        false
% 2.97/0.98  --abstr_ref_until_sat                   false
% 2.97/0.98  --abstr_ref_sig_restrict                funpre
% 2.97/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.97/0.98  --abstr_ref_under                       []
% 2.97/0.98  
% 2.97/0.98  ------ SAT Options
% 2.97/0.98  
% 2.97/0.98  --sat_mode                              false
% 2.97/0.98  --sat_fm_restart_options                ""
% 2.97/0.98  --sat_gr_def                            false
% 2.97/0.98  --sat_epr_types                         true
% 2.97/0.98  --sat_non_cyclic_types                  false
% 2.97/0.98  --sat_finite_models                     false
% 2.97/0.98  --sat_fm_lemmas                         false
% 2.97/0.98  --sat_fm_prep                           false
% 2.97/0.98  --sat_fm_uc_incr                        true
% 2.97/0.98  --sat_out_model                         small
% 2.97/0.98  --sat_out_clauses                       false
% 2.97/0.98  
% 2.97/0.98  ------ QBF Options
% 2.97/0.98  
% 2.97/0.98  --qbf_mode                              false
% 2.97/0.98  --qbf_elim_univ                         false
% 2.97/0.98  --qbf_dom_inst                          none
% 2.97/0.98  --qbf_dom_pre_inst                      false
% 2.97/0.98  --qbf_sk_in                             false
% 2.97/0.98  --qbf_pred_elim                         true
% 2.97/0.98  --qbf_split                             512
% 2.97/0.98  
% 2.97/0.98  ------ BMC1 Options
% 2.97/0.98  
% 2.97/0.98  --bmc1_incremental                      false
% 2.97/0.98  --bmc1_axioms                           reachable_all
% 2.97/0.98  --bmc1_min_bound                        0
% 2.97/0.98  --bmc1_max_bound                        -1
% 2.97/0.98  --bmc1_max_bound_default                -1
% 2.97/0.98  --bmc1_symbol_reachability              true
% 2.97/0.98  --bmc1_property_lemmas                  false
% 2.97/0.98  --bmc1_k_induction                      false
% 2.97/0.98  --bmc1_non_equiv_states                 false
% 2.97/0.98  --bmc1_deadlock                         false
% 2.97/0.98  --bmc1_ucm                              false
% 2.97/0.98  --bmc1_add_unsat_core                   none
% 2.97/0.98  --bmc1_unsat_core_children              false
% 2.97/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.97/0.98  --bmc1_out_stat                         full
% 2.97/0.98  --bmc1_ground_init                      false
% 2.97/0.98  --bmc1_pre_inst_next_state              false
% 2.97/0.98  --bmc1_pre_inst_state                   false
% 2.97/0.98  --bmc1_pre_inst_reach_state             false
% 2.97/0.98  --bmc1_out_unsat_core                   false
% 2.97/0.98  --bmc1_aig_witness_out                  false
% 2.97/0.98  --bmc1_verbose                          false
% 2.97/0.98  --bmc1_dump_clauses_tptp                false
% 2.97/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.97/0.98  --bmc1_dump_file                        -
% 2.97/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.97/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.97/0.98  --bmc1_ucm_extend_mode                  1
% 2.97/0.98  --bmc1_ucm_init_mode                    2
% 2.97/0.98  --bmc1_ucm_cone_mode                    none
% 2.97/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.97/0.98  --bmc1_ucm_relax_model                  4
% 2.97/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.97/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.97/0.98  --bmc1_ucm_layered_model                none
% 2.97/0.98  --bmc1_ucm_max_lemma_size               10
% 2.97/0.98  
% 2.97/0.98  ------ AIG Options
% 2.97/0.98  
% 2.97/0.98  --aig_mode                              false
% 2.97/0.98  
% 2.97/0.98  ------ Instantiation Options
% 2.97/0.98  
% 2.97/0.98  --instantiation_flag                    true
% 2.97/0.98  --inst_sos_flag                         false
% 2.97/0.98  --inst_sos_phase                        true
% 2.97/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.97/0.98  --inst_lit_sel_side                     none
% 2.97/0.98  --inst_solver_per_active                1400
% 2.97/0.98  --inst_solver_calls_frac                1.
% 2.97/0.98  --inst_passive_queue_type               priority_queues
% 2.97/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.97/0.98  --inst_passive_queues_freq              [25;2]
% 2.97/0.98  --inst_dismatching                      true
% 2.97/0.98  --inst_eager_unprocessed_to_passive     true
% 2.97/0.98  --inst_prop_sim_given                   true
% 2.97/0.98  --inst_prop_sim_new                     false
% 2.97/0.98  --inst_subs_new                         false
% 2.97/0.98  --inst_eq_res_simp                      false
% 2.97/0.98  --inst_subs_given                       false
% 2.97/0.98  --inst_orphan_elimination               true
% 2.97/0.98  --inst_learning_loop_flag               true
% 2.97/0.98  --inst_learning_start                   3000
% 2.97/0.98  --inst_learning_factor                  2
% 2.97/0.98  --inst_start_prop_sim_after_learn       3
% 2.97/0.98  --inst_sel_renew                        solver
% 2.97/0.98  --inst_lit_activity_flag                true
% 2.97/0.98  --inst_restr_to_given                   false
% 2.97/0.98  --inst_activity_threshold               500
% 2.97/0.98  --inst_out_proof                        true
% 2.97/0.98  
% 2.97/0.98  ------ Resolution Options
% 2.97/0.98  
% 2.97/0.98  --resolution_flag                       false
% 2.97/0.98  --res_lit_sel                           adaptive
% 2.97/0.98  --res_lit_sel_side                      none
% 2.97/0.98  --res_ordering                          kbo
% 2.97/0.98  --res_to_prop_solver                    active
% 2.97/0.98  --res_prop_simpl_new                    false
% 2.97/0.98  --res_prop_simpl_given                  true
% 2.97/0.98  --res_passive_queue_type                priority_queues
% 2.97/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.97/0.98  --res_passive_queues_freq               [15;5]
% 2.97/0.98  --res_forward_subs                      full
% 2.97/0.98  --res_backward_subs                     full
% 2.97/0.98  --res_forward_subs_resolution           true
% 2.97/0.98  --res_backward_subs_resolution          true
% 2.97/0.98  --res_orphan_elimination                true
% 2.97/0.98  --res_time_limit                        2.
% 2.97/0.98  --res_out_proof                         true
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Options
% 2.97/0.98  
% 2.97/0.98  --superposition_flag                    true
% 2.97/0.98  --sup_passive_queue_type                priority_queues
% 2.97/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.97/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.97/0.98  --demod_completeness_check              fast
% 2.97/0.98  --demod_use_ground                      true
% 2.97/0.98  --sup_to_prop_solver                    passive
% 2.97/0.98  --sup_prop_simpl_new                    true
% 2.97/0.98  --sup_prop_simpl_given                  true
% 2.97/0.98  --sup_fun_splitting                     false
% 2.97/0.98  --sup_smt_interval                      50000
% 2.97/0.98  
% 2.97/0.98  ------ Superposition Simplification Setup
% 2.97/0.98  
% 2.97/0.98  --sup_indices_passive                   []
% 2.97/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.97/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.97/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_full_bw                           [BwDemod]
% 2.97/0.98  --sup_immed_triv                        [TrivRules]
% 2.97/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.97/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_immed_bw_main                     []
% 2.97/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.97/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.97/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.97/0.98  
% 2.97/0.98  ------ Combination Options
% 2.97/0.98  
% 2.97/0.98  --comb_res_mult                         3
% 2.97/0.98  --comb_sup_mult                         2
% 2.97/0.98  --comb_inst_mult                        10
% 2.97/0.98  
% 2.97/0.98  ------ Debug Options
% 2.97/0.98  
% 2.97/0.98  --dbg_backtrace                         false
% 2.97/0.98  --dbg_dump_prop_clauses                 false
% 2.97/0.98  --dbg_dump_prop_clauses_file            -
% 2.97/0.98  --dbg_out_stat                          false
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  ------ Proving...
% 2.97/0.98  
% 2.97/0.98  
% 2.97/0.98  % SZS status Theorem for theBenchmark.p
% 2.97/0.98  
% 2.97/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.97/0.98  
% 2.97/0.98  fof(f21,conjecture,(
% 2.97/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f22,negated_conjecture,(
% 2.97/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 2.97/0.99    inference(negated_conjecture,[],[f21])).
% 2.97/0.99  
% 2.97/0.99  fof(f24,plain,(
% 2.97/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 2.97/0.99    inference(pure_predicate_removal,[],[f22])).
% 2.97/0.99  
% 2.97/0.99  fof(f42,plain,(
% 2.97/0.99    ? [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)))),
% 2.97/0.99    inference(ennf_transformation,[],[f24])).
% 2.97/0.99  
% 2.97/0.99  fof(f43,plain,(
% 2.97/0.99    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1))),
% 2.97/0.99    inference(flattening,[],[f42])).
% 2.97/0.99  
% 2.97/0.99  fof(f58,plain,(
% 2.97/0.99    ? [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) != X0 & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) => (k8_relset_1(sK3,sK4,sK5,sK4) != sK3 & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4))),
% 2.97/0.99    introduced(choice_axiom,[])).
% 2.97/0.99  
% 2.97/0.99  fof(f59,plain,(
% 2.97/0.99    k8_relset_1(sK3,sK4,sK5,sK4) != sK3 & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4)),
% 2.97/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f43,f58])).
% 2.97/0.99  
% 2.97/0.99  fof(f93,plain,(
% 2.97/0.99    v1_funct_2(sK5,sK3,sK4)),
% 2.97/0.99    inference(cnf_transformation,[],[f59])).
% 2.97/0.99  
% 2.97/0.99  fof(f20,axiom,(
% 2.97/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f40,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.99    inference(ennf_transformation,[],[f20])).
% 2.97/0.99  
% 2.97/0.99  fof(f41,plain,(
% 2.97/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.99    inference(flattening,[],[f40])).
% 2.97/0.99  
% 2.97/0.99  fof(f57,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.99    inference(nnf_transformation,[],[f41])).
% 2.97/0.99  
% 2.97/0.99  fof(f87,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f57])).
% 2.97/0.99  
% 2.97/0.99  fof(f94,plain,(
% 2.97/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.97/0.99    inference(cnf_transformation,[],[f59])).
% 2.97/0.99  
% 2.97/0.99  fof(f18,axiom,(
% 2.97/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f38,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.99    inference(ennf_transformation,[],[f18])).
% 2.97/0.99  
% 2.97/0.99  fof(f85,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f38])).
% 2.97/0.99  
% 2.97/0.99  fof(f17,axiom,(
% 2.97/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f23,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.97/0.99    inference(pure_predicate_removal,[],[f17])).
% 2.97/0.99  
% 2.97/0.99  fof(f37,plain,(
% 2.97/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.99    inference(ennf_transformation,[],[f23])).
% 2.97/0.99  
% 2.97/0.99  fof(f84,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f37])).
% 2.97/0.99  
% 2.97/0.99  fof(f10,axiom,(
% 2.97/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f32,plain,(
% 2.97/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.97/0.99    inference(ennf_transformation,[],[f10])).
% 2.97/0.99  
% 2.97/0.99  fof(f56,plain,(
% 2.97/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.97/0.99    inference(nnf_transformation,[],[f32])).
% 2.97/0.99  
% 2.97/0.99  fof(f75,plain,(
% 2.97/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f56])).
% 2.97/0.99  
% 2.97/0.99  fof(f9,axiom,(
% 2.97/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f31,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.97/0.99    inference(ennf_transformation,[],[f9])).
% 2.97/0.99  
% 2.97/0.99  fof(f74,plain,(
% 2.97/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f31])).
% 2.97/0.99  
% 2.97/0.99  fof(f12,axiom,(
% 2.97/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f78,plain,(
% 2.97/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f12])).
% 2.97/0.99  
% 2.97/0.99  fof(f15,axiom,(
% 2.97/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f35,plain,(
% 2.97/0.99    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.97/0.99    inference(ennf_transformation,[],[f15])).
% 2.97/0.99  
% 2.97/0.99  fof(f36,plain,(
% 2.97/0.99    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.97/0.99    inference(flattening,[],[f35])).
% 2.97/0.99  
% 2.97/0.99  fof(f82,plain,(
% 2.97/0.99    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f36])).
% 2.97/0.99  
% 2.97/0.99  fof(f16,axiom,(
% 2.97/0.99    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f25,plain,(
% 2.97/0.99    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.97/0.99    inference(pure_predicate_removal,[],[f16])).
% 2.97/0.99  
% 2.97/0.99  fof(f83,plain,(
% 2.97/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f25])).
% 2.97/0.99  
% 2.97/0.99  fof(f13,axiom,(
% 2.97/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f34,plain,(
% 2.97/0.99    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.97/0.99    inference(ennf_transformation,[],[f13])).
% 2.97/0.99  
% 2.97/0.99  fof(f79,plain,(
% 2.97/0.99    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.97/0.99    inference(cnf_transformation,[],[f34])).
% 2.97/0.99  
% 2.97/0.99  fof(f14,axiom,(
% 2.97/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f80,plain,(
% 2.97/0.99    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.97/0.99    inference(cnf_transformation,[],[f14])).
% 2.97/0.99  
% 2.97/0.99  fof(f19,axiom,(
% 2.97/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.97/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.97/0.99  
% 2.97/0.99  fof(f39,plain,(
% 2.97/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.97/0.99    inference(ennf_transformation,[],[f19])).
% 2.97/0.99  
% 2.97/0.99  fof(f86,plain,(
% 2.97/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f39])).
% 2.97/0.99  
% 2.97/0.99  fof(f96,plain,(
% 2.97/0.99    k8_relset_1(sK3,sK4,sK5,sK4) != sK3),
% 2.97/0.99    inference(cnf_transformation,[],[f59])).
% 2.97/0.99  
% 2.97/0.99  fof(f95,plain,(
% 2.97/0.99    k1_xboole_0 = sK3 | k1_xboole_0 != sK4),
% 2.97/0.99    inference(cnf_transformation,[],[f59])).
% 2.97/0.99  
% 2.97/0.99  fof(f88,plain,(
% 2.97/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.97/0.99    inference(cnf_transformation,[],[f57])).
% 2.97/0.99  
% 2.97/0.99  fof(f103,plain,(
% 2.97/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.97/0.99    inference(equality_resolution,[],[f88])).
% 2.97/0.99  
% 2.97/0.99  cnf(c_36,negated_conjecture,
% 2.97/0.99      ( v1_funct_2(sK5,sK3,sK4) ),
% 2.97/0.99      inference(cnf_transformation,[],[f93]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_32,plain,
% 2.97/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.97/0.99      | k1_xboole_0 = X2 ),
% 2.97/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_35,negated_conjecture,
% 2.97/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.97/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_515,plain,
% 2.97/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.97/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.97/0.99      | sK5 != X0
% 2.97/0.99      | k1_xboole_0 = X2 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_35]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_516,plain,
% 2.97/0.99      ( ~ v1_funct_2(sK5,X0,X1)
% 2.97/0.99      | k1_relset_1(X0,X1,sK5) = X0
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.97/0.99      | k1_xboole_0 = X1 ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_515]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_684,plain,
% 2.97/0.99      ( k1_relset_1(X0,X1,sK5) = X0
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.97/0.99      | sK5 != sK5
% 2.97/0.99      | sK4 != X1
% 2.97/0.99      | sK3 != X0
% 2.97/0.99      | k1_xboole_0 = X1 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_36,c_516]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_685,plain,
% 2.97/0.99      ( k1_relset_1(sK3,sK4,sK5) = sK3
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.97/0.99      | k1_xboole_0 = sK4 ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_684]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1098,plain,
% 2.97/0.99      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 2.97/0.99      inference(equality_resolution_simp,[status(thm)],[c_685]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_25,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_560,plain,
% 2.97/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.97/0.99      | sK5 != X2 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_35]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_561,plain,
% 2.97/0.99      ( k1_relset_1(X0,X1,sK5) = k1_relat_1(sK5)
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_560]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2357,plain,
% 2.97/0.99      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 2.97/0.99      inference(equality_resolution,[status(thm)],[c_561]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2465,plain,
% 2.97/0.99      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_1098,c_2357]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_24,plain,
% 2.97/0.99      ( v5_relat_1(X0,X1)
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.97/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_16,plain,
% 2.97/0.99      ( ~ v5_relat_1(X0,X1)
% 2.97/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 2.97/0.99      | ~ v1_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_456,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 2.97/0.99      | ~ v1_relat_1(X0) ),
% 2.97/0.99      inference(resolution,[status(thm)],[c_24,c_16]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_500,plain,
% 2.97/0.99      ( r1_tarski(k2_relat_1(X0),X1)
% 2.97/0.99      | ~ v1_relat_1(X0)
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.97/0.99      | sK5 != X0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_456,c_35]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_501,plain,
% 2.97/0.99      ( r1_tarski(k2_relat_1(sK5),X0)
% 2.97/0.99      | ~ v1_relat_1(sK5)
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_500]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2149,plain,
% 2.97/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.97/0.99      | r1_tarski(k2_relat_1(sK5),X1) = iProver_top
% 2.97/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_502,plain,
% 2.97/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.97/0.99      | r1_tarski(k2_relat_1(sK5),X1) = iProver_top
% 2.97/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_1596,plain,( X0 = X0 ),theory(equality) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2351,plain,
% 2.97/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_1596]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_14,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.97/0.99      | ~ v1_relat_1(X1)
% 2.97/0.99      | v1_relat_1(X0) ),
% 2.97/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_485,plain,
% 2.97/0.99      ( ~ v1_relat_1(X0)
% 2.97/0.99      | v1_relat_1(X1)
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0)
% 2.97/0.99      | sK5 != X1 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_35]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_486,plain,
% 2.97/0.99      ( ~ v1_relat_1(X0)
% 2.97/0.99      | v1_relat_1(sK5)
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_485]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2346,plain,
% 2.97/0.99      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 2.97/0.99      | v1_relat_1(sK5)
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_486]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2490,plain,
% 2.97/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 2.97/0.99      | v1_relat_1(sK5)
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_2346]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2491,plain,
% 2.97/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.97/0.99      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 2.97/0.99      | v1_relat_1(sK5) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_2490]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_18,plain,
% 2.97/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2575,plain,
% 2.97/0.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.97/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2576,plain,
% 2.97/0.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_2575]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2624,plain,
% 2.97/0.99      ( r1_tarski(k2_relat_1(sK5),X1) = iProver_top
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_2149,c_502,c_2351,c_2491,c_2576]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2625,plain,
% 2.97/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.97/0.99      | r1_tarski(k2_relat_1(sK5),X1) = iProver_top ),
% 2.97/0.99      inference(renaming,[status(thm)],[c_2624]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2632,plain,
% 2.97/0.99      ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top ),
% 2.97/0.99      inference(equality_resolution,[status(thm)],[c_2625]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_22,plain,
% 2.97/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.97/0.99      | ~ v1_relat_1(X0)
% 2.97/0.99      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2153,plain,
% 2.97/0.99      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 2.97/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.97/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3860,plain,
% 2.97/0.99      ( k5_relat_1(sK5,k6_relat_1(sK4)) = sK5
% 2.97/0.99      | v1_relat_1(sK5) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_2632,c_2153]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4190,plain,
% 2.97/0.99      ( k5_relat_1(sK5,k6_relat_1(sK4)) = sK5 ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_3860,c_2351,c_2491,c_2576]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_23,plain,
% 2.97/0.99      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2152,plain,
% 2.97/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2150,plain,
% 2.97/0.99      ( k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) != k1_zfmisc_1(X0)
% 2.97/0.99      | v1_relat_1(X0) != iProver_top
% 2.97/0.99      | v1_relat_1(sK5) = iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2618,plain,
% 2.97/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 2.97/0.99      inference(global_propositional_subsumption,
% 2.97/0.99                [status(thm)],
% 2.97/0.99                [c_2150,c_2351,c_2491,c_2576]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_19,plain,
% 2.97/0.99      ( ~ v1_relat_1(X0)
% 2.97/0.99      | ~ v1_relat_1(X1)
% 2.97/0.99      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 2.97/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2154,plain,
% 2.97/0.99      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 2.97/0.99      | v1_relat_1(X0) != iProver_top
% 2.97/0.99      | v1_relat_1(X1) != iProver_top ),
% 2.97/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_3957,plain,
% 2.97/0.99      ( k10_relat_1(sK5,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK5,X0))
% 2.97/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_2618,c_2154]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4054,plain,
% 2.97/0.99      ( k10_relat_1(sK5,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK5,k6_relat_1(X0))) ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_2152,c_3957]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_21,plain,
% 2.97/0.99      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4059,plain,
% 2.97/0.99      ( k1_relat_1(k5_relat_1(sK5,k6_relat_1(X0))) = k10_relat_1(sK5,X0) ),
% 2.97/0.99      inference(light_normalisation,[status(thm)],[c_4054,c_21]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4282,plain,
% 2.97/0.99      ( k10_relat_1(sK5,sK4) = k1_relat_1(sK5) ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_4190,c_4059]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_26,plain,
% 2.97/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.97/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.97/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_551,plain,
% 2.97/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.97/0.99      | sK5 != X2 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_35]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_552,plain,
% 2.97/0.99      ( k8_relset_1(X0,X1,sK5,X2) = k10_relat_1(sK5,X2)
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_551]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2360,plain,
% 2.97/0.99      ( k8_relset_1(sK3,sK4,sK5,X0) = k10_relat_1(sK5,X0) ),
% 2.97/0.99      inference(equality_resolution,[status(thm)],[c_552]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_33,negated_conjecture,
% 2.97/0.99      ( k8_relset_1(sK3,sK4,sK5,sK4) != sK3 ),
% 2.97/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_2442,plain,
% 2.97/0.99      ( k10_relat_1(sK5,sK4) != sK3 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_2360,c_33]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4333,plain,
% 2.97/0.99      ( k1_relat_1(sK5) != sK3 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_4282,c_2442]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4500,plain,
% 2.97/0.99      ( sK4 = k1_xboole_0 ),
% 2.97/0.99      inference(superposition,[status(thm)],[c_2465,c_4333]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_34,negated_conjecture,
% 2.97/0.99      ( k1_xboole_0 != sK4 | k1_xboole_0 = sK3 ),
% 2.97/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4575,plain,
% 2.97/0.99      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_4500,c_34]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4576,plain,
% 2.97/0.99      ( sK3 = k1_xboole_0 ),
% 2.97/0.99      inference(equality_resolution_simp,[status(thm)],[c_4575]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4648,plain,
% 2.97/0.99      ( k1_relat_1(sK5) != k1_xboole_0 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_4576,c_4333]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4570,plain,
% 2.97/0.99      ( k1_relset_1(sK3,k1_xboole_0,sK5) = k1_relat_1(sK5) ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_4500,c_2357]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_31,plain,
% 2.97/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.97/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.97/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.97/0.99      inference(cnf_transformation,[],[f103]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_604,plain,
% 2.97/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.97/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.97/0.99      | sK5 != X0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_35]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_605,plain,
% 2.97/0.99      ( ~ v1_funct_2(sK5,k1_xboole_0,X0)
% 2.97/0.99      | k1_relset_1(k1_xboole_0,X0,sK5) = k1_xboole_0
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_604]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_709,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,X0,sK5) = k1_xboole_0
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.97/0.99      | sK5 != sK5
% 2.97/0.99      | sK4 != X0
% 2.97/0.99      | sK3 != k1_xboole_0 ),
% 2.97/0.99      inference(resolution_lifted,[status(thm)],[c_36,c_605]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_710,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,sK4,sK5) = k1_xboole_0
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 2.97/0.99      | sK3 != k1_xboole_0 ),
% 2.97/0.99      inference(unflattening,[status(thm)],[c_709]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4572,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.97/0.99      | sK3 != k1_xboole_0 ),
% 2.97/0.99      inference(demodulation,[status(thm)],[c_4500,c_710]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4591,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0
% 2.97/0.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
% 2.97/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 2.97/0.99      inference(light_normalisation,[status(thm)],[c_4572,c_4576]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4592,plain,
% 2.97/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK5) = k1_xboole_0 ),
% 2.97/0.99      inference(equality_resolution_simp,[status(thm)],[c_4591]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(c_4596,plain,
% 2.97/0.99      ( k1_relat_1(sK5) = k1_xboole_0 ),
% 2.97/0.99      inference(light_normalisation,[status(thm)],[c_4570,c_4576,c_4592]) ).
% 2.97/0.99  
% 2.97/0.99  cnf(contradiction,plain,
% 2.97/0.99      ( $false ),
% 2.97/0.99      inference(minisat,[status(thm)],[c_4648,c_4596]) ).
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.97/0.99  
% 2.97/0.99  ------                               Statistics
% 2.97/0.99  
% 2.97/0.99  ------ General
% 2.97/0.99  
% 2.97/0.99  abstr_ref_over_cycles:                  0
% 2.97/0.99  abstr_ref_under_cycles:                 0
% 2.97/0.99  gc_basic_clause_elim:                   0
% 2.97/0.99  forced_gc_time:                         0
% 2.97/0.99  parsing_time:                           0.009
% 2.97/0.99  unif_index_cands_time:                  0.
% 2.97/0.99  unif_index_add_time:                    0.
% 2.97/0.99  orderings_time:                         0.
% 2.97/0.99  out_proof_time:                         0.012
% 2.97/0.99  total_time:                             0.151
% 2.97/0.99  num_of_symbols:                         54
% 2.97/0.99  num_of_terms:                           3607
% 2.97/0.99  
% 2.97/0.99  ------ Preprocessing
% 2.97/0.99  
% 2.97/0.99  num_of_splits:                          0
% 2.97/0.99  num_of_split_atoms:                     0
% 2.97/0.99  num_of_reused_defs:                     0
% 2.97/0.99  num_eq_ax_congr_red:                    29
% 2.97/0.99  num_of_sem_filtered_clauses:            1
% 2.97/0.99  num_of_subtypes:                        0
% 2.97/0.99  monotx_restored_types:                  0
% 2.97/0.99  sat_num_of_epr_types:                   0
% 2.97/0.99  sat_num_of_non_cyclic_types:            0
% 2.97/0.99  sat_guarded_non_collapsed_types:        0
% 2.97/0.99  num_pure_diseq_elim:                    0
% 2.97/0.99  simp_replaced_by:                       0
% 2.97/0.99  res_preprocessed:                       156
% 2.97/0.99  prep_upred:                             0
% 2.97/0.99  prep_unflattend:                        74
% 2.97/0.99  smt_new_axioms:                         0
% 2.97/0.99  pred_elim_cands:                        4
% 2.97/0.99  pred_elim:                              3
% 2.97/0.99  pred_elim_cl:                           7
% 2.97/0.99  pred_elim_cycles:                       5
% 2.97/0.99  merged_defs:                            8
% 2.97/0.99  merged_defs_ncl:                        0
% 2.97/0.99  bin_hyper_res:                          8
% 2.97/0.99  prep_cycles:                            4
% 2.97/0.99  pred_elim_time:                         0.016
% 2.97/0.99  splitting_time:                         0.
% 2.97/0.99  sem_filter_time:                        0.
% 2.97/0.99  monotx_time:                            0.
% 2.97/0.99  subtype_inf_time:                       0.
% 2.97/0.99  
% 2.97/0.99  ------ Problem properties
% 2.97/0.99  
% 2.97/0.99  clauses:                                30
% 2.97/0.99  conjectures:                            2
% 2.97/0.99  epr:                                    5
% 2.97/0.99  horn:                                   25
% 2.97/0.99  ground:                                 7
% 2.97/0.99  unary:                                  8
% 2.97/0.99  binary:                                 13
% 2.97/0.99  lits:                                   62
% 2.97/0.99  lits_eq:                                25
% 2.97/0.99  fd_pure:                                0
% 2.97/0.99  fd_pseudo:                              0
% 2.97/0.99  fd_cond:                                1
% 2.97/0.99  fd_pseudo_cond:                         2
% 2.97/0.99  ac_symbols:                             0
% 2.97/0.99  
% 2.97/0.99  ------ Propositional Solver
% 2.97/0.99  
% 2.97/0.99  prop_solver_calls:                      28
% 2.97/0.99  prop_fast_solver_calls:                 999
% 2.97/0.99  smt_solver_calls:                       0
% 2.97/0.99  smt_fast_solver_calls:                  0
% 2.97/0.99  prop_num_of_clauses:                    1371
% 2.97/0.99  prop_preprocess_simplified:             5472
% 2.97/0.99  prop_fo_subsumed:                       9
% 2.97/0.99  prop_solver_time:                       0.
% 2.97/0.99  smt_solver_time:                        0.
% 2.97/0.99  smt_fast_solver_time:                   0.
% 2.97/0.99  prop_fast_solver_time:                  0.
% 2.97/0.99  prop_unsat_core_time:                   0.
% 2.97/0.99  
% 2.97/0.99  ------ QBF
% 2.97/0.99  
% 2.97/0.99  qbf_q_res:                              0
% 2.97/0.99  qbf_num_tautologies:                    0
% 2.97/0.99  qbf_prep_cycles:                        0
% 2.97/0.99  
% 2.97/0.99  ------ BMC1
% 2.97/0.99  
% 2.97/0.99  bmc1_current_bound:                     -1
% 2.97/0.99  bmc1_last_solved_bound:                 -1
% 2.97/0.99  bmc1_unsat_core_size:                   -1
% 2.97/0.99  bmc1_unsat_core_parents_size:           -1
% 2.97/0.99  bmc1_merge_next_fun:                    0
% 2.97/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.97/0.99  
% 2.97/0.99  ------ Instantiation
% 2.97/0.99  
% 2.97/0.99  inst_num_of_clauses:                    386
% 2.97/0.99  inst_num_in_passive:                    145
% 2.97/0.99  inst_num_in_active:                     222
% 2.97/0.99  inst_num_in_unprocessed:                19
% 2.97/0.99  inst_num_of_loops:                      330
% 2.97/0.99  inst_num_of_learning_restarts:          0
% 2.97/0.99  inst_num_moves_active_passive:          105
% 2.97/0.99  inst_lit_activity:                      0
% 2.97/0.99  inst_lit_activity_moves:                0
% 2.97/0.99  inst_num_tautologies:                   0
% 2.97/0.99  inst_num_prop_implied:                  0
% 2.97/0.99  inst_num_existing_simplified:           0
% 2.97/0.99  inst_num_eq_res_simplified:             0
% 2.97/0.99  inst_num_child_elim:                    0
% 2.97/0.99  inst_num_of_dismatching_blockings:      97
% 2.97/0.99  inst_num_of_non_proper_insts:           367
% 2.97/0.99  inst_num_of_duplicates:                 0
% 2.97/0.99  inst_inst_num_from_inst_to_res:         0
% 2.97/0.99  inst_dismatching_checking_time:         0.
% 2.97/0.99  
% 2.97/0.99  ------ Resolution
% 2.97/0.99  
% 2.97/0.99  res_num_of_clauses:                     0
% 2.97/0.99  res_num_in_passive:                     0
% 2.97/0.99  res_num_in_active:                      0
% 2.97/0.99  res_num_of_loops:                       160
% 2.97/0.99  res_forward_subset_subsumed:            39
% 2.97/0.99  res_backward_subset_subsumed:           0
% 2.97/0.99  res_forward_subsumed:                   0
% 2.97/0.99  res_backward_subsumed:                  0
% 2.97/0.99  res_forward_subsumption_resolution:     1
% 2.97/0.99  res_backward_subsumption_resolution:    0
% 2.97/0.99  res_clause_to_clause_subsumption:       221
% 2.97/0.99  res_orphan_elimination:                 0
% 2.97/0.99  res_tautology_del:                      77
% 2.97/0.99  res_num_eq_res_simplified:              1
% 2.97/0.99  res_num_sel_changes:                    0
% 2.97/0.99  res_moves_from_active_to_pass:          0
% 2.97/0.99  
% 2.97/0.99  ------ Superposition
% 2.97/0.99  
% 2.97/0.99  sup_time_total:                         0.
% 2.97/0.99  sup_time_generating:                    0.
% 2.97/0.99  sup_time_sim_full:                      0.
% 2.97/0.99  sup_time_sim_immed:                     0.
% 2.97/0.99  
% 2.97/0.99  sup_num_of_clauses:                     87
% 2.97/0.99  sup_num_in_active:                      36
% 2.97/0.99  sup_num_in_passive:                     51
% 2.97/0.99  sup_num_of_loops:                       65
% 2.97/0.99  sup_fw_superposition:                   40
% 2.97/0.99  sup_bw_superposition:                   34
% 2.97/0.99  sup_immediate_simplified:               31
% 2.97/0.99  sup_given_eliminated:                   0
% 2.97/0.99  comparisons_done:                       0
% 2.97/0.99  comparisons_avoided:                    6
% 2.97/0.99  
% 2.97/0.99  ------ Simplifications
% 2.97/0.99  
% 2.97/0.99  
% 2.97/0.99  sim_fw_subset_subsumed:                 7
% 2.97/0.99  sim_bw_subset_subsumed:                 1
% 2.97/0.99  sim_fw_subsumed:                        3
% 2.97/0.99  sim_bw_subsumed:                        2
% 2.97/0.99  sim_fw_subsumption_res:                 0
% 2.97/0.99  sim_bw_subsumption_res:                 0
% 2.97/0.99  sim_tautology_del:                      3
% 2.97/0.99  sim_eq_tautology_del:                   2
% 2.97/0.99  sim_eq_res_simp:                        5
% 2.97/0.99  sim_fw_demodulated:                     8
% 2.97/0.99  sim_bw_demodulated:                     30
% 2.97/0.99  sim_light_normalised:                   15
% 2.97/0.99  sim_joinable_taut:                      0
% 2.97/0.99  sim_joinable_simp:                      0
% 2.97/0.99  sim_ac_normalised:                      0
% 2.97/0.99  sim_smt_subsumption:                    0
% 2.97/0.99  
%------------------------------------------------------------------------------
