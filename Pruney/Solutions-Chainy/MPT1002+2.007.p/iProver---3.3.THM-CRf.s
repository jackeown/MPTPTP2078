%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:23 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 303 expanded)
%              Number of clauses        :   63 ( 117 expanded)
%              Number of leaves         :   12 (  55 expanded)
%              Depth                    :   20
%              Number of atoms          :  296 (1244 expanded)
%              Number of equality atoms :  139 ( 415 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2)))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f29])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f52,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_945,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_948,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2059,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_945,c_948])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_956,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1573,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_945,c_956])).

cnf(c_2063,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2059,c_1573])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_25,plain,
    ( v1_funct_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2766,plain,
    ( sK1 = k1_xboole_0
    | k1_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2063,c_25])).

cnf(c_2767,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2766])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_962,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_957,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3417,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_962,c_957])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_954,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2176,plain,
    ( k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_945,c_954])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_947,plain,
    ( r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2354,plain,
    ( r1_tarski(sK2,k10_relat_1(sK3,k7_relset_1(sK0,sK1,sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2176,c_947])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_955,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2193,plain,
    ( k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_945,c_955])).

cnf(c_2628,plain,
    ( r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2354,c_2193])).

cnf(c_4812,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3417,c_2628])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_959,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1419,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_945,c_959])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_154,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_155,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_154])).

cnf(c_200,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_155])).

cnf(c_942,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_200])).

cnf(c_1586,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1419,c_942])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_958,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1856,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1586,c_958])).

cnf(c_4862,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4812,c_24,c_1856])).

cnf(c_4867,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2767,c_4862])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_27,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4969,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4867,c_27])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4979,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4969,c_19])).

cnf(c_4980,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4979])).

cnf(c_946,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5016,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4980,c_946])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_961,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1418,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_961,c_959])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_963,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2091,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1418,c_963])).

cnf(c_5173,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5016,c_2091])).

cnf(c_5181,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5173,c_4862])).

cnf(c_7372,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5181,c_1418])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.23/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.02  
% 3.23/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/1.02  
% 3.23/1.02  ------  iProver source info
% 3.23/1.02  
% 3.23/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.23/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/1.02  git: non_committed_changes: false
% 3.23/1.02  git: last_make_outside_of_git: false
% 3.23/1.02  
% 3.23/1.02  ------ 
% 3.23/1.02  ------ Parsing...
% 3.23/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/1.02  
% 3.23/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.23/1.02  
% 3.23/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/1.02  
% 3.23/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/1.02  ------ Proving...
% 3.23/1.02  ------ Problem Properties 
% 3.23/1.02  
% 3.23/1.02  
% 3.23/1.02  clauses                                 23
% 3.23/1.02  conjectures                             6
% 3.23/1.02  EPR                                     7
% 3.23/1.02  Horn                                    19
% 3.23/1.02  unary                                   8
% 3.23/1.02  binary                                  6
% 3.23/1.02  lits                                    52
% 3.23/1.02  lits eq                                 15
% 3.23/1.02  fd_pure                                 0
% 3.23/1.02  fd_pseudo                               0
% 3.23/1.02  fd_cond                                 3
% 3.23/1.02  fd_pseudo_cond                          1
% 3.23/1.02  AC symbols                              0
% 3.23/1.02  
% 3.23/1.02  ------ Input Options Time Limit: Unbounded
% 3.23/1.02  
% 3.23/1.02  
% 3.23/1.02  ------ 
% 3.23/1.02  Current options:
% 3.23/1.02  ------ 
% 3.23/1.02  
% 3.23/1.02  
% 3.23/1.02  
% 3.23/1.02  
% 3.23/1.02  ------ Proving...
% 3.23/1.02  
% 3.23/1.02  
% 3.23/1.02  % SZS status Theorem for theBenchmark.p
% 3.23/1.02  
% 3.23/1.02   Resolution empty clause
% 3.23/1.02  
% 3.23/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/1.02  
% 3.23/1.02  fof(f12,conjecture,(
% 3.23/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.23/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.02  
% 3.23/1.02  fof(f13,negated_conjecture,(
% 3.23/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => (r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.23/1.02    inference(negated_conjecture,[],[f12])).
% 3.23/1.02  
% 3.23/1.02  fof(f23,plain,(
% 3.23/1.02    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.23/1.02    inference(ennf_transformation,[],[f13])).
% 3.23/1.02  
% 3.23/1.02  fof(f24,plain,(
% 3.23/1.02    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.23/1.02    inference(flattening,[],[f23])).
% 3.23/1.02  
% 3.23/1.02  fof(f29,plain,(
% 3.23/1.02    ? [X0,X1,X2,X3] : (~r1_tarski(X2,k8_relset_1(X0,X1,X3,k7_relset_1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.23/1.02    introduced(choice_axiom,[])).
% 3.23/1.02  
% 3.23/1.02  fof(f30,plain,(
% 3.23/1.02    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.23/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f29])).
% 3.23/1.02  
% 3.23/1.02  fof(f51,plain,(
% 3.23/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.23/1.02    inference(cnf_transformation,[],[f30])).
% 3.23/1.02  
% 3.23/1.02  fof(f11,axiom,(
% 3.23/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.23/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.02  
% 3.23/1.02  fof(f21,plain,(
% 3.23/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.02    inference(ennf_transformation,[],[f11])).
% 3.23/1.02  
% 3.23/1.02  fof(f22,plain,(
% 3.23/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.02    inference(flattening,[],[f21])).
% 3.23/1.02  
% 3.23/1.02  fof(f28,plain,(
% 3.23/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.02    inference(nnf_transformation,[],[f22])).
% 3.23/1.02  
% 3.23/1.02  fof(f43,plain,(
% 3.23/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.02    inference(cnf_transformation,[],[f28])).
% 3.23/1.02  
% 3.23/1.02  fof(f8,axiom,(
% 3.23/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.23/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.02  
% 3.23/1.02  fof(f18,plain,(
% 3.23/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.02    inference(ennf_transformation,[],[f8])).
% 3.23/1.02  
% 3.23/1.02  fof(f40,plain,(
% 3.23/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.02    inference(cnf_transformation,[],[f18])).
% 3.23/1.02  
% 3.23/1.02  fof(f50,plain,(
% 3.23/1.02    v1_funct_2(sK3,sK0,sK1)),
% 3.23/1.02    inference(cnf_transformation,[],[f30])).
% 3.23/1.02  
% 3.23/1.02  fof(f1,axiom,(
% 3.23/1.02    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.23/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.02  
% 3.23/1.02  fof(f25,plain,(
% 3.23/1.02    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/1.02    inference(nnf_transformation,[],[f1])).
% 3.23/1.02  
% 3.23/1.02  fof(f26,plain,(
% 3.23/1.02    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/1.02    inference(flattening,[],[f25])).
% 3.23/1.02  
% 3.23/1.02  fof(f32,plain,(
% 3.23/1.02    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.23/1.02    inference(cnf_transformation,[],[f26])).
% 3.23/1.02  
% 3.23/1.02  fof(f55,plain,(
% 3.23/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.23/1.02    inference(equality_resolution,[],[f32])).
% 3.23/1.02  
% 3.23/1.02  fof(f7,axiom,(
% 3.23/1.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 3.23/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.02  
% 3.23/1.02  fof(f16,plain,(
% 3.23/1.02    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.23/1.02    inference(ennf_transformation,[],[f7])).
% 3.23/1.02  
% 3.23/1.02  fof(f17,plain,(
% 3.23/1.02    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.23/1.02    inference(flattening,[],[f16])).
% 3.23/1.02  
% 3.23/1.02  fof(f39,plain,(
% 3.23/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.23/1.02    inference(cnf_transformation,[],[f17])).
% 3.23/1.02  
% 3.23/1.02  fof(f10,axiom,(
% 3.23/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.23/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.02  
% 3.23/1.02  fof(f20,plain,(
% 3.23/1.02    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.02    inference(ennf_transformation,[],[f10])).
% 3.23/1.02  
% 3.23/1.02  fof(f42,plain,(
% 3.23/1.02    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.02    inference(cnf_transformation,[],[f20])).
% 3.23/1.02  
% 3.23/1.02  fof(f54,plain,(
% 3.23/1.02    ~r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 3.23/1.02    inference(cnf_transformation,[],[f30])).
% 3.23/1.02  
% 3.23/1.02  fof(f9,axiom,(
% 3.23/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.23/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.02  
% 3.23/1.02  fof(f19,plain,(
% 3.23/1.02    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/1.02    inference(ennf_transformation,[],[f9])).
% 3.23/1.02  
% 3.23/1.02  fof(f41,plain,(
% 3.23/1.02    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/1.02    inference(cnf_transformation,[],[f19])).
% 3.23/1.02  
% 3.23/1.02  fof(f49,plain,(
% 3.23/1.02    v1_funct_1(sK3)),
% 3.23/1.02    inference(cnf_transformation,[],[f30])).
% 3.23/1.02  
% 3.23/1.02  fof(f3,axiom,(
% 3.23/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.23/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.02  
% 3.23/1.02  fof(f27,plain,(
% 3.23/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.23/1.02    inference(nnf_transformation,[],[f3])).
% 3.23/1.02  
% 3.23/1.02  fof(f35,plain,(
% 3.23/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.23/1.02    inference(cnf_transformation,[],[f27])).
% 3.23/1.02  
% 3.23/1.02  fof(f5,axiom,(
% 3.23/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.23/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.02  
% 3.23/1.02  fof(f15,plain,(
% 3.23/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.23/1.02    inference(ennf_transformation,[],[f5])).
% 3.23/1.02  
% 3.23/1.02  fof(f37,plain,(
% 3.23/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.23/1.02    inference(cnf_transformation,[],[f15])).
% 3.23/1.02  
% 3.23/1.02  fof(f36,plain,(
% 3.23/1.02    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.23/1.02    inference(cnf_transformation,[],[f27])).
% 3.23/1.02  
% 3.23/1.02  fof(f6,axiom,(
% 3.23/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.23/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.02  
% 3.23/1.02  fof(f38,plain,(
% 3.23/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.23/1.02    inference(cnf_transformation,[],[f6])).
% 3.23/1.02  
% 3.23/1.02  fof(f52,plain,(
% 3.23/1.02    r1_tarski(sK2,sK0)),
% 3.23/1.02    inference(cnf_transformation,[],[f30])).
% 3.23/1.02  
% 3.23/1.02  fof(f53,plain,(
% 3.23/1.02    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.23/1.02    inference(cnf_transformation,[],[f30])).
% 3.23/1.02  
% 3.23/1.02  fof(f2,axiom,(
% 3.23/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.23/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/1.02  
% 3.23/1.02  fof(f34,plain,(
% 3.23/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.23/1.02    inference(cnf_transformation,[],[f2])).
% 3.23/1.02  
% 3.23/1.02  fof(f33,plain,(
% 3.23/1.02    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.23/1.02    inference(cnf_transformation,[],[f26])).
% 3.23/1.02  
% 3.23/1.02  cnf(c_21,negated_conjecture,
% 3.23/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.23/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_945,plain,
% 3.23/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_17,plain,
% 3.23/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.23/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.23/1.02      | k1_xboole_0 = X2 ),
% 3.23/1.02      inference(cnf_transformation,[],[f43]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_948,plain,
% 3.23/1.02      ( k1_relset_1(X0,X1,X2) = X0
% 3.23/1.02      | k1_xboole_0 = X1
% 3.23/1.02      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.23/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_2059,plain,
% 3.23/1.02      ( k1_relset_1(sK0,sK1,sK3) = sK0
% 3.23/1.02      | sK1 = k1_xboole_0
% 3.23/1.02      | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
% 3.23/1.02      inference(superposition,[status(thm)],[c_945,c_948]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_9,plain,
% 3.23/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.23/1.02      inference(cnf_transformation,[],[f40]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_956,plain,
% 3.23/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.23/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1573,plain,
% 3.23/1.02      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.23/1.02      inference(superposition,[status(thm)],[c_945,c_956]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_2063,plain,
% 3.23/1.02      ( k1_relat_1(sK3) = sK0
% 3.23/1.02      | sK1 = k1_xboole_0
% 3.23/1.02      | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
% 3.23/1.02      inference(demodulation,[status(thm)],[c_2059,c_1573]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_22,negated_conjecture,
% 3.23/1.02      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.23/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_25,plain,
% 3.23/1.02      ( v1_funct_2(sK3,sK0,sK1) = iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_2766,plain,
% 3.23/1.02      ( sK1 = k1_xboole_0 | k1_relat_1(sK3) = sK0 ),
% 3.23/1.02      inference(global_propositional_subsumption,[status(thm)],[c_2063,c_25]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_2767,plain,
% 3.23/1.02      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.23/1.02      inference(renaming,[status(thm)],[c_2766]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f55]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_962,plain,
% 3.23/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_8,plain,
% 3.23/1.02      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 3.23/1.02      | ~ r1_tarski(X0,k1_relat_1(X1))
% 3.23/1.02      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 3.23/1.02      | ~ v1_funct_1(X1)
% 3.23/1.02      | ~ v1_relat_1(X1) ),
% 3.23/1.02      inference(cnf_transformation,[],[f39]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_957,plain,
% 3.23/1.02      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 3.23/1.02      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 3.23/1.02      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 3.23/1.02      | v1_funct_1(X1) != iProver_top
% 3.23/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_3417,plain,
% 3.23/1.02      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 3.23/1.02      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 3.23/1.02      | v1_funct_1(X1) != iProver_top
% 3.23/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.23/1.02      inference(superposition,[status(thm)],[c_962,c_957]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_11,plain,
% 3.23/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.02      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.23/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_954,plain,
% 3.23/1.02      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.23/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_2176,plain,
% 3.23/1.02      ( k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0) ),
% 3.23/1.02      inference(superposition,[status(thm)],[c_945,c_954]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_18,negated_conjecture,
% 3.23/1.02      ( ~ r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) ),
% 3.23/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_947,plain,
% 3.23/1.02      ( r1_tarski(sK2,k8_relset_1(sK0,sK1,sK3,k7_relset_1(sK0,sK1,sK3,sK2))) != iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_2354,plain,
% 3.23/1.02      ( r1_tarski(sK2,k10_relat_1(sK3,k7_relset_1(sK0,sK1,sK3,sK2))) != iProver_top ),
% 3.23/1.02      inference(demodulation,[status(thm)],[c_2176,c_947]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_10,plain,
% 3.23/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/1.02      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.23/1.02      inference(cnf_transformation,[],[f41]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_955,plain,
% 3.23/1.02      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.23/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_2193,plain,
% 3.23/1.02      ( k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.23/1.02      inference(superposition,[status(thm)],[c_945,c_955]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_2628,plain,
% 3.23/1.02      ( r1_tarski(sK2,k10_relat_1(sK3,k9_relat_1(sK3,sK2))) != iProver_top ),
% 3.23/1.02      inference(demodulation,[status(thm)],[c_2354,c_2193]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_4812,plain,
% 3.23/1.02      ( r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top
% 3.23/1.02      | v1_funct_1(sK3) != iProver_top
% 3.23/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.23/1.02      inference(superposition,[status(thm)],[c_3417,c_2628]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_23,negated_conjecture,
% 3.23/1.02      ( v1_funct_1(sK3) ),
% 3.23/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_24,plain,
% 3.23/1.02      ( v1_funct_1(sK3) = iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_5,plain,
% 3.23/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.23/1.02      inference(cnf_transformation,[],[f35]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_959,plain,
% 3.23/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.23/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1419,plain,
% 3.23/1.02      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.23/1.02      inference(superposition,[status(thm)],[c_945,c_959]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_6,plain,
% 3.23/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.23/1.02      inference(cnf_transformation,[],[f37]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_4,plain,
% 3.23/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.23/1.02      inference(cnf_transformation,[],[f36]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_154,plain,
% 3.23/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.23/1.02      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_155,plain,
% 3.23/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.23/1.02      inference(renaming,[status(thm)],[c_154]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_200,plain,
% 3.23/1.02      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.23/1.02      inference(bin_hyper_res,[status(thm)],[c_6,c_155]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_942,plain,
% 3.23/1.02      ( r1_tarski(X0,X1) != iProver_top
% 3.23/1.02      | v1_relat_1(X1) != iProver_top
% 3.23/1.02      | v1_relat_1(X0) = iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_200]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1586,plain,
% 3.23/1.02      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.23/1.02      | v1_relat_1(sK3) = iProver_top ),
% 3.23/1.02      inference(superposition,[status(thm)],[c_1419,c_942]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_7,plain,
% 3.23/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.23/1.02      inference(cnf_transformation,[],[f38]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_958,plain,
% 3.23/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1856,plain,
% 3.23/1.02      ( v1_relat_1(sK3) = iProver_top ),
% 3.23/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_1586,c_958]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_4862,plain,
% 3.23/1.02      ( r1_tarski(sK2,k1_relat_1(sK3)) != iProver_top ),
% 3.23/1.02      inference(global_propositional_subsumption,
% 3.23/1.02                [status(thm)],
% 3.23/1.02                [c_4812,c_24,c_1856]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_4867,plain,
% 3.23/1.02      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK0) != iProver_top ),
% 3.23/1.02      inference(superposition,[status(thm)],[c_2767,c_4862]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_20,negated_conjecture,
% 3.23/1.02      ( r1_tarski(sK2,sK0) ),
% 3.23/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_27,plain,
% 3.23/1.02      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_4969,plain,
% 3.23/1.02      ( sK1 = k1_xboole_0 ),
% 3.23/1.02      inference(global_propositional_subsumption,[status(thm)],[c_4867,c_27]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_19,negated_conjecture,
% 3.23/1.02      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.23/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_4979,plain,
% 3.23/1.02      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.23/1.02      inference(demodulation,[status(thm)],[c_4969,c_19]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_4980,plain,
% 3.23/1.02      ( sK0 = k1_xboole_0 ),
% 3.23/1.02      inference(equality_resolution_simp,[status(thm)],[c_4979]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_946,plain,
% 3.23/1.02      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_5016,plain,
% 3.23/1.02      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.23/1.02      inference(demodulation,[status(thm)],[c_4980,c_946]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_3,plain,
% 3.23/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.23/1.02      inference(cnf_transformation,[],[f34]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_961,plain,
% 3.23/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1418,plain,
% 3.23/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.23/1.02      inference(superposition,[status(thm)],[c_961,c_959]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_0,plain,
% 3.23/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.23/1.02      inference(cnf_transformation,[],[f33]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_963,plain,
% 3.23/1.02      ( X0 = X1
% 3.23/1.02      | r1_tarski(X0,X1) != iProver_top
% 3.23/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_2091,plain,
% 3.23/1.02      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.23/1.02      inference(superposition,[status(thm)],[c_1418,c_963]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_5173,plain,
% 3.23/1.02      ( sK2 = k1_xboole_0 ),
% 3.23/1.02      inference(superposition,[status(thm)],[c_5016,c_2091]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_5181,plain,
% 3.23/1.02      ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top ),
% 3.23/1.02      inference(demodulation,[status(thm)],[c_5173,c_4862]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_7372,plain,
% 3.23/1.02      ( $false ),
% 3.23/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_5181,c_1418]) ).
% 3.23/1.02  
% 3.23/1.02  
% 3.23/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/1.02  
% 3.23/1.02  ------                               Statistics
% 3.23/1.02  
% 3.23/1.02  ------ Selected
% 3.23/1.02  
% 3.23/1.02  total_time:                             0.244
% 3.23/1.02  
%------------------------------------------------------------------------------
