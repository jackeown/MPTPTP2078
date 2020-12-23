%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:38 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 229 expanded)
%              Number of clauses        :   62 (  92 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :   18
%              Number of atoms          :  296 ( 778 expanded)
%              Number of equality atoms :   92 ( 183 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
              | ~ m1_subset_1(X3,X1) )
          & k1_xboole_0 != k1_relset_1(X0,X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(X0,X1,sK3))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k1_relset_1(X0,X1,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k2_relset_1(X0,sK2,X2))
                | ~ m1_subset_1(X3,sK2) )
            & k1_xboole_0 != k1_relset_1(X0,sK2,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) )
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k1_relset_1(X0,X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(sK1,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(sK1,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK1,sK2,sK3))
        | ~ m1_subset_1(X3,sK2) )
    & k1_xboole_0 != k1_relset_1(sK1,sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f37,f36,f35])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f31])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK1,sK2,sK3))
      | ~ m1_subset_1(X3,sK2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    k1_xboole_0 != k1_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1270,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_289,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_8])).

cnf(c_1265,plain,
    ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_2005,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1270,c_1265])).

cnf(c_22,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1396,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1397,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1396])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_149,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_187,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_149])).

cnf(c_1436,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_1643,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_1644,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1643])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1699,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1700,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1699])).

cnf(c_2167,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2005,c_22,c_1397,c_1644,c_1700])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_257,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X3
    | sK0(X3) != X0
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X0),X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_420,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_452,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(sK0(X0),X1)
    | k1_xboole_0 = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_258,c_420])).

cnf(c_1264,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(sK0(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_452])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1271,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1716,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1270,c_1271])).

cnf(c_15,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,sK2)
    | k2_relset_1(sK1,sK2,sK3) != X1
    | sK0(X1) != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_273,plain,
    ( ~ m1_subset_1(sK0(k2_relset_1(sK1,sK2,sK3)),sK2)
    | k1_xboole_0 = k2_relset_1(sK1,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_1266,plain,
    ( k1_xboole_0 = k2_relset_1(sK1,sK2,sK3)
    | m1_subset_1(sK0(k2_relset_1(sK1,sK2,sK3)),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_1783,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK0(k2_relat_1(sK3)),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1716,c_1266])).

cnf(c_1788,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1264,c_1783])).

cnf(c_2172,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2167,c_1788])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1273,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2236,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2172,c_1273])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_62,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2316,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2236,c_22,c_62,c_1397,c_1644,c_1700])).

cnf(c_1279,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1278,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1670,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1279,c_1278])).

cnf(c_2322,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2316,c_1670])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1272,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2034,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1270,c_1272])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != k1_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2124,plain,
    ( k1_relat_1(sK3) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2034,c_16])).

cnf(c_2376,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2322,c_2124])).

cnf(c_9,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1275,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1884,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1275,c_1670])).

cnf(c_1934,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1279,c_1884])).

cnf(c_2388,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2376,c_1934])).

cnf(c_2389,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2388])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:24:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.90/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/0.98  
% 1.90/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.90/0.98  
% 1.90/0.98  ------  iProver source info
% 1.90/0.98  
% 1.90/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.90/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.90/0.98  git: non_committed_changes: false
% 1.90/0.98  git: last_make_outside_of_git: false
% 1.90/0.98  
% 1.90/0.98  ------ 
% 1.90/0.98  
% 1.90/0.98  ------ Input Options
% 1.90/0.98  
% 1.90/0.98  --out_options                           all
% 1.90/0.98  --tptp_safe_out                         true
% 1.90/0.98  --problem_path                          ""
% 1.90/0.98  --include_path                          ""
% 1.90/0.98  --clausifier                            res/vclausify_rel
% 1.90/0.98  --clausifier_options                    --mode clausify
% 1.90/0.98  --stdin                                 false
% 1.90/0.98  --stats_out                             all
% 1.90/0.98  
% 1.90/0.98  ------ General Options
% 1.90/0.98  
% 1.90/0.98  --fof                                   false
% 1.90/0.98  --time_out_real                         305.
% 1.90/0.98  --time_out_virtual                      -1.
% 1.90/0.98  --symbol_type_check                     false
% 1.90/0.98  --clausify_out                          false
% 1.90/0.98  --sig_cnt_out                           false
% 1.90/0.98  --trig_cnt_out                          false
% 1.90/0.98  --trig_cnt_out_tolerance                1.
% 1.90/0.98  --trig_cnt_out_sk_spl                   false
% 1.90/0.98  --abstr_cl_out                          false
% 1.90/0.98  
% 1.90/0.98  ------ Global Options
% 1.90/0.98  
% 1.90/0.98  --schedule                              default
% 1.90/0.98  --add_important_lit                     false
% 1.90/0.98  --prop_solver_per_cl                    1000
% 1.90/0.98  --min_unsat_core                        false
% 1.90/0.98  --soft_assumptions                      false
% 1.90/0.98  --soft_lemma_size                       3
% 1.90/0.98  --prop_impl_unit_size                   0
% 1.90/0.98  --prop_impl_unit                        []
% 1.90/0.98  --share_sel_clauses                     true
% 1.90/0.98  --reset_solvers                         false
% 1.90/0.98  --bc_imp_inh                            [conj_cone]
% 1.90/0.98  --conj_cone_tolerance                   3.
% 1.90/0.98  --extra_neg_conj                        none
% 1.90/0.98  --large_theory_mode                     true
% 1.90/0.98  --prolific_symb_bound                   200
% 1.90/0.98  --lt_threshold                          2000
% 1.90/0.98  --clause_weak_htbl                      true
% 1.90/0.98  --gc_record_bc_elim                     false
% 1.90/0.98  
% 1.90/0.98  ------ Preprocessing Options
% 1.90/0.98  
% 1.90/0.98  --preprocessing_flag                    true
% 1.90/0.98  --time_out_prep_mult                    0.1
% 1.90/0.98  --splitting_mode                        input
% 1.90/0.98  --splitting_grd                         true
% 1.90/0.98  --splitting_cvd                         false
% 1.90/0.98  --splitting_cvd_svl                     false
% 1.90/0.98  --splitting_nvd                         32
% 1.90/0.98  --sub_typing                            true
% 1.90/0.98  --prep_gs_sim                           true
% 1.90/0.98  --prep_unflatten                        true
% 1.90/0.98  --prep_res_sim                          true
% 1.90/0.98  --prep_upred                            true
% 1.90/0.98  --prep_sem_filter                       exhaustive
% 1.90/0.98  --prep_sem_filter_out                   false
% 1.90/0.98  --pred_elim                             true
% 1.90/0.98  --res_sim_input                         true
% 1.90/0.98  --eq_ax_congr_red                       true
% 1.90/0.98  --pure_diseq_elim                       true
% 1.90/0.98  --brand_transform                       false
% 1.90/0.98  --non_eq_to_eq                          false
% 1.90/0.98  --prep_def_merge                        true
% 1.90/0.98  --prep_def_merge_prop_impl              false
% 1.90/0.98  --prep_def_merge_mbd                    true
% 1.90/0.98  --prep_def_merge_tr_red                 false
% 1.90/0.98  --prep_def_merge_tr_cl                  false
% 1.90/0.98  --smt_preprocessing                     true
% 1.90/0.98  --smt_ac_axioms                         fast
% 1.90/0.98  --preprocessed_out                      false
% 1.90/0.98  --preprocessed_stats                    false
% 1.90/0.98  
% 1.90/0.98  ------ Abstraction refinement Options
% 1.90/0.98  
% 1.90/0.98  --abstr_ref                             []
% 1.90/0.98  --abstr_ref_prep                        false
% 1.90/0.98  --abstr_ref_until_sat                   false
% 1.90/0.98  --abstr_ref_sig_restrict                funpre
% 1.90/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.90/0.98  --abstr_ref_under                       []
% 1.90/0.98  
% 1.90/0.98  ------ SAT Options
% 1.90/0.98  
% 1.90/0.98  --sat_mode                              false
% 1.90/0.98  --sat_fm_restart_options                ""
% 1.90/0.98  --sat_gr_def                            false
% 1.90/0.98  --sat_epr_types                         true
% 1.90/0.98  --sat_non_cyclic_types                  false
% 1.90/0.98  --sat_finite_models                     false
% 1.90/0.98  --sat_fm_lemmas                         false
% 1.90/0.98  --sat_fm_prep                           false
% 1.90/0.98  --sat_fm_uc_incr                        true
% 1.90/0.98  --sat_out_model                         small
% 1.90/0.98  --sat_out_clauses                       false
% 1.90/0.98  
% 1.90/0.98  ------ QBF Options
% 1.90/0.98  
% 1.90/0.98  --qbf_mode                              false
% 1.90/0.98  --qbf_elim_univ                         false
% 1.90/0.98  --qbf_dom_inst                          none
% 1.90/0.98  --qbf_dom_pre_inst                      false
% 1.90/0.98  --qbf_sk_in                             false
% 1.90/0.98  --qbf_pred_elim                         true
% 1.90/0.98  --qbf_split                             512
% 1.90/0.98  
% 1.90/0.98  ------ BMC1 Options
% 1.90/0.98  
% 1.90/0.98  --bmc1_incremental                      false
% 1.90/0.98  --bmc1_axioms                           reachable_all
% 1.90/0.98  --bmc1_min_bound                        0
% 1.90/0.98  --bmc1_max_bound                        -1
% 1.90/0.98  --bmc1_max_bound_default                -1
% 1.90/0.98  --bmc1_symbol_reachability              true
% 1.90/0.98  --bmc1_property_lemmas                  false
% 1.90/0.98  --bmc1_k_induction                      false
% 1.90/0.98  --bmc1_non_equiv_states                 false
% 1.90/0.98  --bmc1_deadlock                         false
% 1.90/0.98  --bmc1_ucm                              false
% 1.90/0.98  --bmc1_add_unsat_core                   none
% 1.90/0.98  --bmc1_unsat_core_children              false
% 1.90/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.90/0.98  --bmc1_out_stat                         full
% 1.90/0.98  --bmc1_ground_init                      false
% 1.90/0.98  --bmc1_pre_inst_next_state              false
% 1.90/0.98  --bmc1_pre_inst_state                   false
% 1.90/0.98  --bmc1_pre_inst_reach_state             false
% 1.90/0.98  --bmc1_out_unsat_core                   false
% 1.90/0.98  --bmc1_aig_witness_out                  false
% 1.90/0.98  --bmc1_verbose                          false
% 1.90/0.98  --bmc1_dump_clauses_tptp                false
% 1.90/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.90/0.98  --bmc1_dump_file                        -
% 1.90/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.90/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.90/0.98  --bmc1_ucm_extend_mode                  1
% 1.90/0.98  --bmc1_ucm_init_mode                    2
% 1.90/0.98  --bmc1_ucm_cone_mode                    none
% 1.90/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.90/0.98  --bmc1_ucm_relax_model                  4
% 1.90/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.90/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.90/0.98  --bmc1_ucm_layered_model                none
% 1.90/0.98  --bmc1_ucm_max_lemma_size               10
% 1.90/0.98  
% 1.90/0.98  ------ AIG Options
% 1.90/0.98  
% 1.90/0.98  --aig_mode                              false
% 1.90/0.98  
% 1.90/0.98  ------ Instantiation Options
% 1.90/0.98  
% 1.90/0.98  --instantiation_flag                    true
% 1.90/0.98  --inst_sos_flag                         false
% 1.90/0.98  --inst_sos_phase                        true
% 1.90/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.90/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.90/0.98  --inst_lit_sel_side                     num_symb
% 1.90/0.98  --inst_solver_per_active                1400
% 1.90/0.98  --inst_solver_calls_frac                1.
% 1.90/0.98  --inst_passive_queue_type               priority_queues
% 1.90/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.90/0.98  --inst_passive_queues_freq              [25;2]
% 1.90/0.98  --inst_dismatching                      true
% 1.90/0.98  --inst_eager_unprocessed_to_passive     true
% 1.90/0.98  --inst_prop_sim_given                   true
% 1.90/0.98  --inst_prop_sim_new                     false
% 1.90/0.98  --inst_subs_new                         false
% 1.90/0.98  --inst_eq_res_simp                      false
% 1.90/0.98  --inst_subs_given                       false
% 1.90/0.98  --inst_orphan_elimination               true
% 1.90/0.98  --inst_learning_loop_flag               true
% 1.90/0.98  --inst_learning_start                   3000
% 1.90/0.98  --inst_learning_factor                  2
% 1.90/0.98  --inst_start_prop_sim_after_learn       3
% 1.90/0.98  --inst_sel_renew                        solver
% 1.90/0.98  --inst_lit_activity_flag                true
% 1.90/0.98  --inst_restr_to_given                   false
% 1.90/0.98  --inst_activity_threshold               500
% 1.90/0.98  --inst_out_proof                        true
% 1.90/0.98  
% 1.90/0.98  ------ Resolution Options
% 1.90/0.98  
% 1.90/0.98  --resolution_flag                       true
% 1.90/0.98  --res_lit_sel                           adaptive
% 1.90/0.98  --res_lit_sel_side                      none
% 1.90/0.98  --res_ordering                          kbo
% 1.90/0.98  --res_to_prop_solver                    active
% 1.90/0.98  --res_prop_simpl_new                    false
% 1.90/0.98  --res_prop_simpl_given                  true
% 1.90/0.98  --res_passive_queue_type                priority_queues
% 1.90/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.90/0.98  --res_passive_queues_freq               [15;5]
% 1.90/0.98  --res_forward_subs                      full
% 1.90/0.98  --res_backward_subs                     full
% 1.90/0.98  --res_forward_subs_resolution           true
% 1.90/0.98  --res_backward_subs_resolution          true
% 1.90/0.98  --res_orphan_elimination                true
% 1.90/0.98  --res_time_limit                        2.
% 1.90/0.98  --res_out_proof                         true
% 1.90/0.98  
% 1.90/0.98  ------ Superposition Options
% 1.90/0.98  
% 1.90/0.98  --superposition_flag                    true
% 1.90/0.98  --sup_passive_queue_type                priority_queues
% 1.90/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.90/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.90/0.98  --demod_completeness_check              fast
% 1.90/0.98  --demod_use_ground                      true
% 1.90/0.98  --sup_to_prop_solver                    passive
% 1.90/0.98  --sup_prop_simpl_new                    true
% 1.90/0.98  --sup_prop_simpl_given                  true
% 1.90/0.98  --sup_fun_splitting                     false
% 1.90/0.98  --sup_smt_interval                      50000
% 1.90/0.98  
% 1.90/0.98  ------ Superposition Simplification Setup
% 1.90/0.98  
% 1.90/0.98  --sup_indices_passive                   []
% 1.90/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.90/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.98  --sup_full_bw                           [BwDemod]
% 1.90/0.98  --sup_immed_triv                        [TrivRules]
% 1.90/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.90/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.98  --sup_immed_bw_main                     []
% 1.90/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.90/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/0.98  
% 1.90/0.98  ------ Combination Options
% 1.90/0.98  
% 1.90/0.98  --comb_res_mult                         3
% 1.90/0.98  --comb_sup_mult                         2
% 1.90/0.98  --comb_inst_mult                        10
% 1.90/0.98  
% 1.90/0.98  ------ Debug Options
% 1.90/0.98  
% 1.90/0.98  --dbg_backtrace                         false
% 1.90/0.98  --dbg_dump_prop_clauses                 false
% 1.90/0.98  --dbg_dump_prop_clauses_file            -
% 1.90/0.98  --dbg_out_stat                          false
% 1.90/0.98  ------ Parsing...
% 1.90/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.90/0.98  
% 1.90/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.90/0.98  
% 1.90/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.90/0.98  
% 1.90/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.90/0.98  ------ Proving...
% 1.90/0.98  ------ Problem Properties 
% 1.90/0.98  
% 1.90/0.98  
% 1.90/0.98  clauses                                 17
% 1.90/0.98  conjectures                             4
% 1.90/0.98  EPR                                     5
% 1.90/0.98  Horn                                    16
% 1.90/0.98  unary                                   6
% 1.90/0.98  binary                                  6
% 1.90/0.98  lits                                    33
% 1.90/0.98  lits eq                                 6
% 1.90/0.98  fd_pure                                 0
% 1.90/0.98  fd_pseudo                               0
% 1.90/0.98  fd_cond                                 1
% 1.90/0.98  fd_pseudo_cond                          1
% 1.90/0.98  AC symbols                              0
% 1.90/0.98  
% 1.90/0.98  ------ Schedule dynamic 5 is on 
% 1.90/0.98  
% 1.90/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.90/0.98  
% 1.90/0.98  
% 1.90/0.98  ------ 
% 1.90/0.98  Current options:
% 1.90/0.98  ------ 
% 1.90/0.98  
% 1.90/0.98  ------ Input Options
% 1.90/0.98  
% 1.90/0.98  --out_options                           all
% 1.90/0.98  --tptp_safe_out                         true
% 1.90/0.98  --problem_path                          ""
% 1.90/0.98  --include_path                          ""
% 1.90/0.98  --clausifier                            res/vclausify_rel
% 1.90/0.98  --clausifier_options                    --mode clausify
% 1.90/0.98  --stdin                                 false
% 1.90/0.98  --stats_out                             all
% 1.90/0.98  
% 1.90/0.98  ------ General Options
% 1.90/0.98  
% 1.90/0.98  --fof                                   false
% 1.90/0.98  --time_out_real                         305.
% 1.90/0.98  --time_out_virtual                      -1.
% 1.90/0.98  --symbol_type_check                     false
% 1.90/0.98  --clausify_out                          false
% 1.90/0.98  --sig_cnt_out                           false
% 1.90/0.98  --trig_cnt_out                          false
% 1.90/0.98  --trig_cnt_out_tolerance                1.
% 1.90/0.98  --trig_cnt_out_sk_spl                   false
% 1.90/0.98  --abstr_cl_out                          false
% 1.90/0.98  
% 1.90/0.98  ------ Global Options
% 1.90/0.98  
% 1.90/0.98  --schedule                              default
% 1.90/0.98  --add_important_lit                     false
% 1.90/0.98  --prop_solver_per_cl                    1000
% 1.90/0.98  --min_unsat_core                        false
% 1.90/0.98  --soft_assumptions                      false
% 1.90/0.98  --soft_lemma_size                       3
% 1.90/0.98  --prop_impl_unit_size                   0
% 1.90/0.98  --prop_impl_unit                        []
% 1.90/0.98  --share_sel_clauses                     true
% 1.90/0.98  --reset_solvers                         false
% 1.90/0.98  --bc_imp_inh                            [conj_cone]
% 1.90/0.98  --conj_cone_tolerance                   3.
% 1.90/0.98  --extra_neg_conj                        none
% 1.90/0.98  --large_theory_mode                     true
% 1.90/0.98  --prolific_symb_bound                   200
% 1.90/0.98  --lt_threshold                          2000
% 1.90/0.98  --clause_weak_htbl                      true
% 1.90/0.98  --gc_record_bc_elim                     false
% 1.90/0.98  
% 1.90/0.98  ------ Preprocessing Options
% 1.90/0.98  
% 1.90/0.98  --preprocessing_flag                    true
% 1.90/0.98  --time_out_prep_mult                    0.1
% 1.90/0.98  --splitting_mode                        input
% 1.90/0.98  --splitting_grd                         true
% 1.90/0.98  --splitting_cvd                         false
% 1.90/0.98  --splitting_cvd_svl                     false
% 1.90/0.98  --splitting_nvd                         32
% 1.90/0.98  --sub_typing                            true
% 1.90/0.98  --prep_gs_sim                           true
% 1.90/0.98  --prep_unflatten                        true
% 1.90/0.98  --prep_res_sim                          true
% 1.90/0.98  --prep_upred                            true
% 1.90/0.98  --prep_sem_filter                       exhaustive
% 1.90/0.98  --prep_sem_filter_out                   false
% 1.90/0.98  --pred_elim                             true
% 1.90/0.98  --res_sim_input                         true
% 1.90/0.98  --eq_ax_congr_red                       true
% 1.90/0.98  --pure_diseq_elim                       true
% 1.90/0.98  --brand_transform                       false
% 1.90/0.98  --non_eq_to_eq                          false
% 1.90/0.98  --prep_def_merge                        true
% 1.90/0.98  --prep_def_merge_prop_impl              false
% 1.90/0.98  --prep_def_merge_mbd                    true
% 1.90/0.98  --prep_def_merge_tr_red                 false
% 1.90/0.98  --prep_def_merge_tr_cl                  false
% 1.90/0.98  --smt_preprocessing                     true
% 1.90/0.98  --smt_ac_axioms                         fast
% 1.90/0.98  --preprocessed_out                      false
% 1.90/0.98  --preprocessed_stats                    false
% 1.90/0.98  
% 1.90/0.98  ------ Abstraction refinement Options
% 1.90/0.98  
% 1.90/0.98  --abstr_ref                             []
% 1.90/0.98  --abstr_ref_prep                        false
% 1.90/0.98  --abstr_ref_until_sat                   false
% 1.90/0.98  --abstr_ref_sig_restrict                funpre
% 1.90/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.90/0.98  --abstr_ref_under                       []
% 1.90/0.98  
% 1.90/0.98  ------ SAT Options
% 1.90/0.98  
% 1.90/0.98  --sat_mode                              false
% 1.90/0.98  --sat_fm_restart_options                ""
% 1.90/0.98  --sat_gr_def                            false
% 1.90/0.98  --sat_epr_types                         true
% 1.90/0.98  --sat_non_cyclic_types                  false
% 1.90/0.98  --sat_finite_models                     false
% 1.90/0.98  --sat_fm_lemmas                         false
% 1.90/0.98  --sat_fm_prep                           false
% 1.90/0.98  --sat_fm_uc_incr                        true
% 1.90/0.98  --sat_out_model                         small
% 1.90/0.98  --sat_out_clauses                       false
% 1.90/0.98  
% 1.90/0.98  ------ QBF Options
% 1.90/0.98  
% 1.90/0.98  --qbf_mode                              false
% 1.90/0.98  --qbf_elim_univ                         false
% 1.90/0.98  --qbf_dom_inst                          none
% 1.90/0.98  --qbf_dom_pre_inst                      false
% 1.90/0.98  --qbf_sk_in                             false
% 1.90/0.98  --qbf_pred_elim                         true
% 1.90/0.98  --qbf_split                             512
% 1.90/0.98  
% 1.90/0.98  ------ BMC1 Options
% 1.90/0.98  
% 1.90/0.98  --bmc1_incremental                      false
% 1.90/0.98  --bmc1_axioms                           reachable_all
% 1.90/0.98  --bmc1_min_bound                        0
% 1.90/0.98  --bmc1_max_bound                        -1
% 1.90/0.98  --bmc1_max_bound_default                -1
% 1.90/0.98  --bmc1_symbol_reachability              true
% 1.90/0.98  --bmc1_property_lemmas                  false
% 1.90/0.98  --bmc1_k_induction                      false
% 1.90/0.98  --bmc1_non_equiv_states                 false
% 1.90/0.98  --bmc1_deadlock                         false
% 1.90/0.98  --bmc1_ucm                              false
% 1.90/0.98  --bmc1_add_unsat_core                   none
% 1.90/0.98  --bmc1_unsat_core_children              false
% 1.90/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.90/0.98  --bmc1_out_stat                         full
% 1.90/0.98  --bmc1_ground_init                      false
% 1.90/0.98  --bmc1_pre_inst_next_state              false
% 1.90/0.98  --bmc1_pre_inst_state                   false
% 1.90/0.98  --bmc1_pre_inst_reach_state             false
% 1.90/0.98  --bmc1_out_unsat_core                   false
% 1.90/0.98  --bmc1_aig_witness_out                  false
% 1.90/0.98  --bmc1_verbose                          false
% 1.90/0.98  --bmc1_dump_clauses_tptp                false
% 1.90/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.90/0.98  --bmc1_dump_file                        -
% 1.90/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.90/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.90/0.98  --bmc1_ucm_extend_mode                  1
% 1.90/0.98  --bmc1_ucm_init_mode                    2
% 1.90/0.98  --bmc1_ucm_cone_mode                    none
% 1.90/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.90/0.98  --bmc1_ucm_relax_model                  4
% 1.90/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.90/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.90/0.98  --bmc1_ucm_layered_model                none
% 1.90/0.98  --bmc1_ucm_max_lemma_size               10
% 1.90/0.98  
% 1.90/0.98  ------ AIG Options
% 1.90/0.98  
% 1.90/0.98  --aig_mode                              false
% 1.90/0.98  
% 1.90/0.98  ------ Instantiation Options
% 1.90/0.98  
% 1.90/0.98  --instantiation_flag                    true
% 1.90/0.98  --inst_sos_flag                         false
% 1.90/0.98  --inst_sos_phase                        true
% 1.90/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.90/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.90/0.98  --inst_lit_sel_side                     none
% 1.90/0.98  --inst_solver_per_active                1400
% 1.90/0.98  --inst_solver_calls_frac                1.
% 1.90/0.98  --inst_passive_queue_type               priority_queues
% 1.90/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.90/0.98  --inst_passive_queues_freq              [25;2]
% 1.90/0.98  --inst_dismatching                      true
% 1.90/0.98  --inst_eager_unprocessed_to_passive     true
% 1.90/0.98  --inst_prop_sim_given                   true
% 1.90/0.98  --inst_prop_sim_new                     false
% 1.90/0.98  --inst_subs_new                         false
% 1.90/0.98  --inst_eq_res_simp                      false
% 1.90/0.98  --inst_subs_given                       false
% 1.90/0.98  --inst_orphan_elimination               true
% 1.90/0.98  --inst_learning_loop_flag               true
% 1.90/0.98  --inst_learning_start                   3000
% 1.90/0.98  --inst_learning_factor                  2
% 1.90/0.98  --inst_start_prop_sim_after_learn       3
% 1.90/0.98  --inst_sel_renew                        solver
% 1.90/0.98  --inst_lit_activity_flag                true
% 1.90/0.98  --inst_restr_to_given                   false
% 1.90/0.98  --inst_activity_threshold               500
% 1.90/0.98  --inst_out_proof                        true
% 1.90/0.98  
% 1.90/0.98  ------ Resolution Options
% 1.90/0.98  
% 1.90/0.98  --resolution_flag                       false
% 1.90/0.98  --res_lit_sel                           adaptive
% 1.90/0.98  --res_lit_sel_side                      none
% 1.90/0.98  --res_ordering                          kbo
% 1.90/0.98  --res_to_prop_solver                    active
% 1.90/0.98  --res_prop_simpl_new                    false
% 1.90/0.98  --res_prop_simpl_given                  true
% 1.90/0.98  --res_passive_queue_type                priority_queues
% 1.90/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.90/0.98  --res_passive_queues_freq               [15;5]
% 1.90/0.98  --res_forward_subs                      full
% 1.90/0.98  --res_backward_subs                     full
% 1.90/0.98  --res_forward_subs_resolution           true
% 1.90/0.98  --res_backward_subs_resolution          true
% 1.90/0.98  --res_orphan_elimination                true
% 1.90/0.98  --res_time_limit                        2.
% 1.90/0.98  --res_out_proof                         true
% 1.90/0.98  
% 1.90/0.98  ------ Superposition Options
% 1.90/0.98  
% 1.90/0.98  --superposition_flag                    true
% 1.90/0.98  --sup_passive_queue_type                priority_queues
% 1.90/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.90/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.90/0.98  --demod_completeness_check              fast
% 1.90/0.98  --demod_use_ground                      true
% 1.90/0.98  --sup_to_prop_solver                    passive
% 1.90/0.98  --sup_prop_simpl_new                    true
% 1.90/0.98  --sup_prop_simpl_given                  true
% 1.90/0.98  --sup_fun_splitting                     false
% 1.90/0.98  --sup_smt_interval                      50000
% 1.90/0.98  
% 1.90/0.98  ------ Superposition Simplification Setup
% 1.90/0.98  
% 1.90/0.98  --sup_indices_passive                   []
% 1.90/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.90/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.90/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.98  --sup_full_bw                           [BwDemod]
% 1.90/0.98  --sup_immed_triv                        [TrivRules]
% 1.90/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.90/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.98  --sup_immed_bw_main                     []
% 1.90/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.90/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.90/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.90/0.98  
% 1.90/0.98  ------ Combination Options
% 1.90/0.98  
% 1.90/0.98  --comb_res_mult                         3
% 1.90/0.98  --comb_sup_mult                         2
% 1.90/0.98  --comb_inst_mult                        10
% 1.90/0.98  
% 1.90/0.98  ------ Debug Options
% 1.90/0.98  
% 1.90/0.98  --dbg_backtrace                         false
% 1.90/0.98  --dbg_dump_prop_clauses                 false
% 1.90/0.98  --dbg_dump_prop_clauses_file            -
% 1.90/0.98  --dbg_out_stat                          false
% 1.90/0.98  
% 1.90/0.98  
% 1.90/0.98  
% 1.90/0.98  
% 1.90/0.98  ------ Proving...
% 1.90/0.98  
% 1.90/0.98  
% 1.90/0.98  % SZS status Theorem for theBenchmark.p
% 1.90/0.98  
% 1.90/0.98   Resolution empty clause
% 1.90/0.98  
% 1.90/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.90/0.98  
% 1.90/0.98  fof(f14,conjecture,(
% 1.90/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 1.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.98  
% 1.90/0.98  fof(f15,negated_conjecture,(
% 1.90/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 1.90/0.98    inference(negated_conjecture,[],[f14])).
% 1.90/0.98  
% 1.90/0.98  fof(f29,plain,(
% 1.90/0.98    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.90/0.98    inference(ennf_transformation,[],[f15])).
% 1.90/0.98  
% 1.90/0.98  fof(f30,plain,(
% 1.90/0.98    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.90/0.98    inference(flattening,[],[f29])).
% 1.90/0.98  
% 1.90/0.98  fof(f37,plain,(
% 1.90/0.98    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,sK3)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) )),
% 1.90/0.98    introduced(choice_axiom,[])).
% 1.90/0.98  
% 1.90/0.98  fof(f36,plain,(
% 1.90/0.98    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,sK2,X2)) | ~m1_subset_1(X3,sK2)) & k1_xboole_0 != k1_relset_1(X0,sK2,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) & ~v1_xboole_0(sK2))) )),
% 1.90/0.98    introduced(choice_axiom,[])).
% 1.90/0.98  
% 1.90/0.98  fof(f35,plain,(
% 1.90/0.98    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK1,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK1,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 1.90/0.98    introduced(choice_axiom,[])).
% 1.90/0.98  
% 1.90/0.98  fof(f38,plain,(
% 1.90/0.98    ((! [X3] : (~r2_hidden(X3,k2_relset_1(sK1,sK2,sK3)) | ~m1_subset_1(X3,sK2)) & k1_xboole_0 != k1_relset_1(sK1,sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 1.90/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f37,f36,f35])).
% 1.90/0.98  
% 1.90/0.98  fof(f56,plain,(
% 1.90/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.90/0.98    inference(cnf_transformation,[],[f38])).
% 1.90/0.98  
% 1.90/0.98  fof(f11,axiom,(
% 1.90/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.98  
% 1.90/0.98  fof(f16,plain,(
% 1.90/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.90/0.98    inference(pure_predicate_removal,[],[f11])).
% 1.90/0.98  
% 1.90/0.98  fof(f26,plain,(
% 1.90/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.98    inference(ennf_transformation,[],[f16])).
% 1.90/0.98  
% 1.90/0.98  fof(f51,plain,(
% 1.90/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.90/0.98    inference(cnf_transformation,[],[f26])).
% 1.90/0.98  
% 1.90/0.98  fof(f7,axiom,(
% 1.90/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.98  
% 1.90/0.98  fof(f22,plain,(
% 1.90/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.90/0.98    inference(ennf_transformation,[],[f7])).
% 1.90/0.98  
% 1.90/0.98  fof(f34,plain,(
% 1.90/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.90/0.98    inference(nnf_transformation,[],[f22])).
% 1.90/0.98  
% 1.90/0.98  fof(f46,plain,(
% 1.90/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.90/0.98    inference(cnf_transformation,[],[f34])).
% 1.90/0.98  
% 1.90/0.98  fof(f4,axiom,(
% 1.90/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.98  
% 1.90/0.98  fof(f33,plain,(
% 1.90/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.90/0.98    inference(nnf_transformation,[],[f4])).
% 1.90/0.98  
% 1.90/0.98  fof(f42,plain,(
% 1.90/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.90/0.98    inference(cnf_transformation,[],[f33])).
% 1.90/0.98  
% 1.90/0.98  fof(f6,axiom,(
% 1.90/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.98  
% 1.90/0.98  fof(f21,plain,(
% 1.90/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.90/0.98    inference(ennf_transformation,[],[f6])).
% 1.90/0.98  
% 1.90/0.98  fof(f45,plain,(
% 1.90/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.90/0.98    inference(cnf_transformation,[],[f21])).
% 1.90/0.98  
% 1.90/0.98  fof(f43,plain,(
% 1.90/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.90/0.98    inference(cnf_transformation,[],[f33])).
% 1.90/0.98  
% 1.90/0.98  fof(f9,axiom,(
% 1.90/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.98  
% 1.90/0.98  fof(f49,plain,(
% 1.90/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.90/0.98    inference(cnf_transformation,[],[f9])).
% 1.90/0.98  
% 1.90/0.98  fof(f2,axiom,(
% 1.90/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.98  
% 1.90/0.98  fof(f17,plain,(
% 1.90/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.90/0.98    inference(ennf_transformation,[],[f2])).
% 1.90/0.98  
% 1.90/0.98  fof(f31,plain,(
% 1.90/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.90/0.98    introduced(choice_axiom,[])).
% 1.90/0.98  
% 1.90/0.98  fof(f32,plain,(
% 1.90/0.98    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 1.90/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f31])).
% 1.90/0.98  
% 1.90/0.98  fof(f40,plain,(
% 1.90/0.98    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.90/0.98    inference(cnf_transformation,[],[f32])).
% 1.90/0.98  
% 1.90/0.98  fof(f5,axiom,(
% 1.90/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.98  
% 1.90/0.98  fof(f19,plain,(
% 1.90/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.90/0.98    inference(ennf_transformation,[],[f5])).
% 1.90/0.98  
% 1.90/0.98  fof(f20,plain,(
% 1.90/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.90/0.98    inference(flattening,[],[f19])).
% 1.90/0.98  
% 1.90/0.98  fof(f44,plain,(
% 1.90/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.90/0.98    inference(cnf_transformation,[],[f20])).
% 1.90/0.98  
% 1.90/0.98  fof(f13,axiom,(
% 1.90/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.98  
% 1.90/0.98  fof(f28,plain,(
% 1.90/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.98    inference(ennf_transformation,[],[f13])).
% 1.90/0.98  
% 1.90/0.98  fof(f53,plain,(
% 1.90/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.90/0.98    inference(cnf_transformation,[],[f28])).
% 1.90/0.98  
% 1.90/0.98  fof(f58,plain,(
% 1.90/0.98    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK1,sK2,sK3)) | ~m1_subset_1(X3,sK2)) )),
% 1.90/0.98    inference(cnf_transformation,[],[f38])).
% 1.90/0.98  
% 1.90/0.98  fof(f10,axiom,(
% 1.90/0.98    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 1.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.98  
% 1.90/0.98  fof(f24,plain,(
% 1.90/0.98    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.90/0.98    inference(ennf_transformation,[],[f10])).
% 1.90/0.98  
% 1.90/0.98  fof(f25,plain,(
% 1.90/0.98    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.90/0.98    inference(flattening,[],[f24])).
% 1.90/0.98  
% 1.90/0.98  fof(f50,plain,(
% 1.90/0.98    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.90/0.98    inference(cnf_transformation,[],[f25])).
% 1.90/0.98  
% 1.90/0.98  fof(f1,axiom,(
% 1.90/0.98    v1_xboole_0(k1_xboole_0)),
% 1.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.98  
% 1.90/0.98  fof(f39,plain,(
% 1.90/0.98    v1_xboole_0(k1_xboole_0)),
% 1.90/0.98    inference(cnf_transformation,[],[f1])).
% 1.90/0.98  
% 1.90/0.98  fof(f3,axiom,(
% 1.90/0.98    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.98  
% 1.90/0.98  fof(f18,plain,(
% 1.90/0.98    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.90/0.98    inference(ennf_transformation,[],[f3])).
% 1.90/0.98  
% 1.90/0.98  fof(f41,plain,(
% 1.90/0.98    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.90/0.98    inference(cnf_transformation,[],[f18])).
% 1.90/0.98  
% 1.90/0.98  fof(f12,axiom,(
% 1.90/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.98  
% 1.90/0.98  fof(f27,plain,(
% 1.90/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.98    inference(ennf_transformation,[],[f12])).
% 1.90/0.98  
% 1.90/0.98  fof(f52,plain,(
% 1.90/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.90/0.98    inference(cnf_transformation,[],[f27])).
% 1.90/0.98  
% 1.90/0.98  fof(f57,plain,(
% 1.90/0.98    k1_xboole_0 != k1_relset_1(sK1,sK2,sK3)),
% 1.90/0.98    inference(cnf_transformation,[],[f38])).
% 1.90/0.98  
% 1.90/0.98  fof(f8,axiom,(
% 1.90/0.98    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 1.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.90/0.98  
% 1.90/0.98  fof(f23,plain,(
% 1.90/0.98    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.90/0.98    inference(ennf_transformation,[],[f8])).
% 1.90/0.98  
% 1.90/0.98  fof(f48,plain,(
% 1.90/0.98    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.90/0.98    inference(cnf_transformation,[],[f23])).
% 1.90/0.98  
% 1.90/0.98  cnf(c_17,negated_conjecture,
% 1.90/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.90/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1270,plain,
% 1.90/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.90/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_12,plain,
% 1.90/0.98      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.90/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_8,plain,
% 1.90/0.98      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 1.90/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_289,plain,
% 1.90/0.98      ( r1_tarski(k2_relat_1(X0),X1)
% 1.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.90/0.98      | ~ v1_relat_1(X0) ),
% 1.90/0.98      inference(resolution,[status(thm)],[c_12,c_8]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1265,plain,
% 1.90/0.98      ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 1.90/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 1.90/0.98      | v1_relat_1(X0) != iProver_top ),
% 1.90/0.98      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_2005,plain,
% 1.90/0.98      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 1.90/0.98      | v1_relat_1(sK3) != iProver_top ),
% 1.90/0.98      inference(superposition,[status(thm)],[c_1270,c_1265]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_22,plain,
% 1.90/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.90/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_4,plain,
% 1.90/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.90/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1396,plain,
% 1.90/0.98      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
% 1.90/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.90/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1397,plain,
% 1.90/0.98      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top
% 1.90/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 1.90/0.98      inference(predicate_to_equality,[status(thm)],[c_1396]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_6,plain,
% 1.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 1.90/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_3,plain,
% 1.90/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.90/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_149,plain,
% 1.90/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.90/0.98      inference(prop_impl,[status(thm)],[c_3]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_187,plain,
% 1.90/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 1.90/0.98      inference(bin_hyper_res,[status(thm)],[c_6,c_149]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1436,plain,
% 1.90/0.98      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 1.90/0.98      | v1_relat_1(X0)
% 1.90/0.98      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 1.90/0.98      inference(instantiation,[status(thm)],[c_187]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1643,plain,
% 1.90/0.98      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))
% 1.90/0.98      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 1.90/0.98      | v1_relat_1(sK3) ),
% 1.90/0.98      inference(instantiation,[status(thm)],[c_1436]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1644,plain,
% 1.90/0.98      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) != iProver_top
% 1.90/0.98      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 1.90/0.98      | v1_relat_1(sK3) = iProver_top ),
% 1.90/0.98      inference(predicate_to_equality,[status(thm)],[c_1643]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_10,plain,
% 1.90/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.90/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1699,plain,
% 1.90/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.90/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1700,plain,
% 1.90/0.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 1.90/0.98      inference(predicate_to_equality,[status(thm)],[c_1699]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_2167,plain,
% 1.90/0.98      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 1.90/0.98      inference(global_propositional_subsumption,
% 1.90/0.98                [status(thm)],
% 1.90/0.98                [c_2005,c_22,c_1397,c_1644,c_1700]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1,plain,
% 1.90/0.98      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.90/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_5,plain,
% 1.90/0.98      ( m1_subset_1(X0,X1)
% 1.90/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.90/0.98      | ~ r2_hidden(X0,X2) ),
% 1.90/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_257,plain,
% 1.90/0.98      ( m1_subset_1(X0,X1)
% 1.90/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.90/0.98      | X2 != X3
% 1.90/0.98      | sK0(X3) != X0
% 1.90/0.98      | k1_xboole_0 = X3 ),
% 1.90/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_5]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_258,plain,
% 1.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.90/0.98      | m1_subset_1(sK0(X0),X1)
% 1.90/0.98      | k1_xboole_0 = X0 ),
% 1.90/0.98      inference(unflattening,[status(thm)],[c_257]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_420,plain,
% 1.90/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.90/0.98      inference(prop_impl,[status(thm)],[c_3]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_452,plain,
% 1.90/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(sK0(X0),X1) | k1_xboole_0 = X0 ),
% 1.90/0.98      inference(bin_hyper_res,[status(thm)],[c_258,c_420]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1264,plain,
% 1.90/0.98      ( k1_xboole_0 = X0
% 1.90/0.98      | r1_tarski(X0,X1) != iProver_top
% 1.90/0.98      | m1_subset_1(sK0(X0),X1) = iProver_top ),
% 1.90/0.98      inference(predicate_to_equality,[status(thm)],[c_452]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_14,plain,
% 1.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.90/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.90/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1271,plain,
% 1.90/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.90/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.90/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1716,plain,
% 1.90/0.98      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 1.90/0.98      inference(superposition,[status(thm)],[c_1270,c_1271]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_15,negated_conjecture,
% 1.90/0.98      ( ~ m1_subset_1(X0,sK2) | ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3)) ),
% 1.90/0.98      inference(cnf_transformation,[],[f58]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_272,plain,
% 1.90/0.98      ( ~ m1_subset_1(X0,sK2)
% 1.90/0.98      | k2_relset_1(sK1,sK2,sK3) != X1
% 1.90/0.98      | sK0(X1) != X0
% 1.90/0.98      | k1_xboole_0 = X1 ),
% 1.90/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_15]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_273,plain,
% 1.90/0.98      ( ~ m1_subset_1(sK0(k2_relset_1(sK1,sK2,sK3)),sK2)
% 1.90/0.98      | k1_xboole_0 = k2_relset_1(sK1,sK2,sK3) ),
% 1.90/0.98      inference(unflattening,[status(thm)],[c_272]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1266,plain,
% 1.90/0.98      ( k1_xboole_0 = k2_relset_1(sK1,sK2,sK3)
% 1.90/0.98      | m1_subset_1(sK0(k2_relset_1(sK1,sK2,sK3)),sK2) != iProver_top ),
% 1.90/0.98      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1783,plain,
% 1.90/0.98      ( k2_relat_1(sK3) = k1_xboole_0
% 1.90/0.98      | m1_subset_1(sK0(k2_relat_1(sK3)),sK2) != iProver_top ),
% 1.90/0.98      inference(demodulation,[status(thm)],[c_1716,c_1266]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1788,plain,
% 1.90/0.98      ( k2_relat_1(sK3) = k1_xboole_0
% 1.90/0.98      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 1.90/0.98      inference(superposition,[status(thm)],[c_1264,c_1783]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_2172,plain,
% 1.90/0.98      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 1.90/0.98      inference(superposition,[status(thm)],[c_2167,c_1788]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_11,plain,
% 1.90/0.98      ( ~ v1_relat_1(X0) | v1_xboole_0(X0) | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 1.90/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1273,plain,
% 1.90/0.98      ( v1_relat_1(X0) != iProver_top
% 1.90/0.98      | v1_xboole_0(X0) = iProver_top
% 1.90/0.98      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 1.90/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_2236,plain,
% 1.90/0.98      ( v1_relat_1(sK3) != iProver_top
% 1.90/0.98      | v1_xboole_0(sK3) = iProver_top
% 1.90/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.90/0.98      inference(superposition,[status(thm)],[c_2172,c_1273]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_0,plain,
% 1.90/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 1.90/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_62,plain,
% 1.90/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.90/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_2316,plain,
% 1.90/0.98      ( v1_xboole_0(sK3) = iProver_top ),
% 1.90/0.98      inference(global_propositional_subsumption,
% 1.90/0.98                [status(thm)],
% 1.90/0.98                [c_2236,c_22,c_62,c_1397,c_1644,c_1700]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1279,plain,
% 1.90/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.90/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_2,plain,
% 1.90/0.98      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 1.90/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1278,plain,
% 1.90/0.98      ( X0 = X1
% 1.90/0.98      | v1_xboole_0(X0) != iProver_top
% 1.90/0.98      | v1_xboole_0(X1) != iProver_top ),
% 1.90/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1670,plain,
% 1.90/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 1.90/0.98      inference(superposition,[status(thm)],[c_1279,c_1278]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_2322,plain,
% 1.90/0.98      ( sK3 = k1_xboole_0 ),
% 1.90/0.98      inference(superposition,[status(thm)],[c_2316,c_1670]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_13,plain,
% 1.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.90/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.90/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1272,plain,
% 1.90/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.90/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.90/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_2034,plain,
% 1.90/0.98      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 1.90/0.98      inference(superposition,[status(thm)],[c_1270,c_1272]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_16,negated_conjecture,
% 1.90/0.98      ( k1_xboole_0 != k1_relset_1(sK1,sK2,sK3) ),
% 1.90/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_2124,plain,
% 1.90/0.98      ( k1_relat_1(sK3) != k1_xboole_0 ),
% 1.90/0.98      inference(demodulation,[status(thm)],[c_2034,c_16]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_2376,plain,
% 1.90/0.98      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 1.90/0.98      inference(demodulation,[status(thm)],[c_2322,c_2124]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_9,plain,
% 1.90/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0)) ),
% 1.90/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1275,plain,
% 1.90/0.98      ( v1_xboole_0(X0) != iProver_top
% 1.90/0.98      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 1.90/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1884,plain,
% 1.90/0.98      ( k1_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 1.90/0.98      inference(superposition,[status(thm)],[c_1275,c_1670]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_1934,plain,
% 1.90/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.90/0.98      inference(superposition,[status(thm)],[c_1279,c_1884]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_2388,plain,
% 1.90/0.98      ( k1_xboole_0 != k1_xboole_0 ),
% 1.90/0.98      inference(light_normalisation,[status(thm)],[c_2376,c_1934]) ).
% 1.90/0.98  
% 1.90/0.98  cnf(c_2389,plain,
% 1.90/0.98      ( $false ),
% 1.90/0.98      inference(equality_resolution_simp,[status(thm)],[c_2388]) ).
% 1.90/0.98  
% 1.90/0.98  
% 1.90/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.90/0.98  
% 1.90/0.98  ------                               Statistics
% 1.90/0.98  
% 1.90/0.98  ------ General
% 1.90/0.98  
% 1.90/0.98  abstr_ref_over_cycles:                  0
% 1.90/0.98  abstr_ref_under_cycles:                 0
% 1.90/0.98  gc_basic_clause_elim:                   0
% 1.90/0.98  forced_gc_time:                         0
% 1.90/0.98  parsing_time:                           0.009
% 1.90/0.98  unif_index_cands_time:                  0.
% 1.90/0.98  unif_index_add_time:                    0.
% 1.90/0.98  orderings_time:                         0.
% 1.90/0.98  out_proof_time:                         0.009
% 1.90/0.98  total_time:                             0.092
% 1.90/0.98  num_of_symbols:                         48
% 1.90/0.98  num_of_terms:                           1506
% 1.90/0.98  
% 1.90/0.98  ------ Preprocessing
% 1.90/0.98  
% 1.90/0.98  num_of_splits:                          0
% 1.90/0.98  num_of_split_atoms:                     0
% 1.90/0.98  num_of_reused_defs:                     0
% 1.90/0.98  num_eq_ax_congr_red:                    12
% 1.90/0.98  num_of_sem_filtered_clauses:            1
% 1.90/0.98  num_of_subtypes:                        0
% 1.90/0.98  monotx_restored_types:                  0
% 1.90/0.98  sat_num_of_epr_types:                   0
% 1.90/0.98  sat_num_of_non_cyclic_types:            0
% 1.90/0.98  sat_guarded_non_collapsed_types:        0
% 1.90/0.98  num_pure_diseq_elim:                    0
% 1.90/0.98  simp_replaced_by:                       0
% 1.90/0.98  res_preprocessed:                       94
% 1.90/0.98  prep_upred:                             0
% 1.90/0.98  prep_unflattend:                        31
% 1.90/0.98  smt_new_axioms:                         0
% 1.90/0.98  pred_elim_cands:                        4
% 1.90/0.98  pred_elim:                              2
% 1.90/0.98  pred_elim_cl:                           3
% 1.90/0.98  pred_elim_cycles:                       5
% 1.90/0.98  merged_defs:                            8
% 1.90/0.98  merged_defs_ncl:                        0
% 1.90/0.98  bin_hyper_res:                          10
% 1.90/0.98  prep_cycles:                            4
% 1.90/0.98  pred_elim_time:                         0.007
% 1.90/0.98  splitting_time:                         0.
% 1.90/0.98  sem_filter_time:                        0.
% 1.90/0.98  monotx_time:                            0.
% 1.90/0.98  subtype_inf_time:                       0.
% 1.90/0.98  
% 1.90/0.98  ------ Problem properties
% 1.90/0.98  
% 1.90/0.98  clauses:                                17
% 1.90/0.98  conjectures:                            4
% 1.90/0.98  epr:                                    5
% 1.90/0.98  horn:                                   16
% 1.90/0.98  ground:                                 6
% 1.90/0.98  unary:                                  6
% 1.90/0.98  binary:                                 6
% 1.90/0.98  lits:                                   33
% 1.90/0.98  lits_eq:                                6
% 1.90/0.98  fd_pure:                                0
% 1.90/0.98  fd_pseudo:                              0
% 1.90/0.98  fd_cond:                                1
% 1.90/0.98  fd_pseudo_cond:                         1
% 1.90/0.98  ac_symbols:                             0
% 1.90/0.98  
% 1.90/0.98  ------ Propositional Solver
% 1.90/0.98  
% 1.90/0.98  prop_solver_calls:                      27
% 1.90/0.98  prop_fast_solver_calls:                 541
% 1.90/0.98  smt_solver_calls:                       0
% 1.90/0.98  smt_fast_solver_calls:                  0
% 1.90/0.98  prop_num_of_clauses:                    621
% 1.90/0.98  prop_preprocess_simplified:             3147
% 1.90/0.98  prop_fo_subsumed:                       3
% 1.90/0.98  prop_solver_time:                       0.
% 1.90/0.98  smt_solver_time:                        0.
% 1.90/0.98  smt_fast_solver_time:                   0.
% 1.90/0.98  prop_fast_solver_time:                  0.
% 1.90/0.98  prop_unsat_core_time:                   0.
% 1.90/0.98  
% 1.90/0.98  ------ QBF
% 1.90/0.98  
% 1.90/0.98  qbf_q_res:                              0
% 1.90/0.98  qbf_num_tautologies:                    0
% 1.90/0.98  qbf_prep_cycles:                        0
% 1.90/0.98  
% 1.90/0.98  ------ BMC1
% 1.90/0.98  
% 1.90/0.98  bmc1_current_bound:                     -1
% 1.90/0.98  bmc1_last_solved_bound:                 -1
% 1.90/0.98  bmc1_unsat_core_size:                   -1
% 1.90/0.98  bmc1_unsat_core_parents_size:           -1
% 1.90/0.98  bmc1_merge_next_fun:                    0
% 1.90/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.90/0.98  
% 1.90/0.98  ------ Instantiation
% 1.90/0.98  
% 1.90/0.98  inst_num_of_clauses:                    213
% 1.90/0.98  inst_num_in_passive:                    38
% 1.90/0.98  inst_num_in_active:                     151
% 1.90/0.98  inst_num_in_unprocessed:                24
% 1.90/0.98  inst_num_of_loops:                      160
% 1.90/0.98  inst_num_of_learning_restarts:          0
% 1.90/0.98  inst_num_moves_active_passive:          6
% 1.90/0.98  inst_lit_activity:                      0
% 1.90/0.98  inst_lit_activity_moves:                0
% 1.90/0.98  inst_num_tautologies:                   0
% 1.90/0.98  inst_num_prop_implied:                  0
% 1.90/0.98  inst_num_existing_simplified:           0
% 1.90/0.98  inst_num_eq_res_simplified:             0
% 1.90/0.98  inst_num_child_elim:                    0
% 1.90/0.98  inst_num_of_dismatching_blockings:      52
% 1.90/0.98  inst_num_of_non_proper_insts:           253
% 1.90/0.98  inst_num_of_duplicates:                 0
% 1.90/0.98  inst_inst_num_from_inst_to_res:         0
% 1.90/0.98  inst_dismatching_checking_time:         0.
% 1.90/0.98  
% 1.90/0.98  ------ Resolution
% 1.90/0.98  
% 1.90/0.98  res_num_of_clauses:                     0
% 1.90/0.98  res_num_in_passive:                     0
% 1.90/0.98  res_num_in_active:                      0
% 1.90/0.98  res_num_of_loops:                       98
% 1.90/0.98  res_forward_subset_subsumed:            43
% 1.90/0.98  res_backward_subset_subsumed:           0
% 1.90/0.98  res_forward_subsumed:                   0
% 1.90/0.98  res_backward_subsumed:                  0
% 1.90/0.98  res_forward_subsumption_resolution:     0
% 1.90/0.98  res_backward_subsumption_resolution:    0
% 1.90/0.98  res_clause_to_clause_subsumption:       78
% 1.90/0.98  res_orphan_elimination:                 0
% 1.90/0.98  res_tautology_del:                      49
% 1.90/0.98  res_num_eq_res_simplified:              0
% 1.90/0.98  res_num_sel_changes:                    0
% 1.90/0.98  res_moves_from_active_to_pass:          0
% 1.90/0.98  
% 1.90/0.98  ------ Superposition
% 1.90/0.98  
% 1.90/0.98  sup_time_total:                         0.
% 1.90/0.98  sup_time_generating:                    0.
% 1.90/0.98  sup_time_sim_full:                      0.
% 1.90/0.98  sup_time_sim_immed:                     0.
% 1.90/0.98  
% 1.90/0.98  sup_num_of_clauses:                     29
% 1.90/0.98  sup_num_in_active:                      17
% 1.90/0.98  sup_num_in_passive:                     12
% 1.90/0.98  sup_num_of_loops:                       30
% 1.90/0.98  sup_fw_superposition:                   18
% 1.90/0.98  sup_bw_superposition:                   8
% 1.90/0.98  sup_immediate_simplified:               1
% 1.90/0.98  sup_given_eliminated:                   1
% 1.90/0.98  comparisons_done:                       0
% 1.90/0.98  comparisons_avoided:                    0
% 1.90/0.98  
% 1.90/0.98  ------ Simplifications
% 1.90/0.98  
% 1.90/0.98  
% 1.90/0.98  sim_fw_subset_subsumed:                 1
% 1.90/0.98  sim_bw_subset_subsumed:                 3
% 1.90/0.98  sim_fw_subsumed:                        0
% 1.90/0.98  sim_bw_subsumed:                        0
% 1.90/0.98  sim_fw_subsumption_res:                 0
% 1.90/0.98  sim_bw_subsumption_res:                 0
% 1.90/0.98  sim_tautology_del:                      0
% 1.90/0.98  sim_eq_tautology_del:                   1
% 1.90/0.98  sim_eq_res_simp:                        0
% 1.90/0.98  sim_fw_demodulated:                     1
% 1.90/0.98  sim_bw_demodulated:                     12
% 1.90/0.98  sim_light_normalised:                   3
% 1.90/0.98  sim_joinable_taut:                      0
% 1.90/0.98  sim_joinable_simp:                      0
% 1.90/0.98  sim_ac_normalised:                      0
% 1.90/0.98  sim_smt_subsumption:                    0
% 1.90/0.98  
%------------------------------------------------------------------------------
