%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:50 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 264 expanded)
%              Number of clauses        :   61 (  98 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  308 ( 838 expanded)
%              Number of equality atoms :  118 ( 210 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
            & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f26])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k2_relset_1(X1,X0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(sK2,sK1,sK3))
          | ~ m1_subset_1(X3,sK2) )
      & k1_xboole_0 != k2_relset_1(sK2,sK1,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_relset_1(sK2,sK1,sK3))
        | ~ m1_subset_1(X3,sK2) )
    & k1_xboole_0 != k2_relset_1(sK2,sK1,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f37])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK2,sK1,sK3))
      | ~ m1_subset_1(X3,sK2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    k1_xboole_0 != k2_relset_1(sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_912,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_275,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_12])).

cnf(c_910,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_275])).

cnf(c_1283,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_912,c_910])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_926,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_925,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1920,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_925])).

cnf(c_3347,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1920,c_925])).

cnf(c_4714,plain,
    ( r2_hidden(sK0(k1_relat_1(sK3),X0),X1) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK2,X1) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_3347])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_920,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1226,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_912,c_920])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_164,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_165,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_164])).

cnf(c_203,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_165])).

cnf(c_911,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_1625,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_911])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_918,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1647,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1625,c_918])).

cnf(c_921,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_919,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1942,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_921,c_919])).

cnf(c_3691,plain,
    ( m1_subset_1(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_1942])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_915,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1811,plain,
    ( k1_relset_1(sK2,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_912,c_915])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,k1_relset_1(sK2,sK1,sK3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_913,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,k1_relset_1(sK2,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1377,plain,
    ( m1_subset_1(sK0(k1_relset_1(sK2,sK1,sK3),X0),sK2) != iProver_top
    | r1_tarski(k1_relset_1(sK2,sK1,sK3),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_926,c_913])).

cnf(c_2110,plain,
    ( m1_subset_1(sK0(k1_relat_1(sK3),X0),sK2) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1811,c_1377])).

cnf(c_4762,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3691,c_2110])).

cnf(c_5320,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4714,c_1283,c_1647,c_4762])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_922,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_924,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1896,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_922,c_924])).

cnf(c_5330,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5320,c_1896])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2767,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1648,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1647])).

cnf(c_460,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1233,plain,
    ( k2_relat_1(sK3) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_1234,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1233])).

cnf(c_1074,plain,
    ( k2_relset_1(sK2,sK1,sK3) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k2_relset_1(sK2,sK1,sK3) ),
    inference(instantiation,[status(thm)],[c_460])).

cnf(c_1133,plain,
    ( k2_relset_1(sK2,sK1,sK3) != k2_relat_1(sK3)
    | k1_xboole_0 = k2_relset_1(sK2,sK1,sK3)
    | k1_xboole_0 != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1090,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_relset_1(sK2,sK1,sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_66,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_61,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != k2_relset_1(sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5330,c_2767,c_1648,c_1234,c_1133,c_1090,c_66,c_61,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.31/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.00  
% 2.31/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.31/1.00  
% 2.31/1.00  ------  iProver source info
% 2.31/1.00  
% 2.31/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.31/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.31/1.00  git: non_committed_changes: false
% 2.31/1.00  git: last_make_outside_of_git: false
% 2.31/1.00  
% 2.31/1.00  ------ 
% 2.31/1.00  
% 2.31/1.00  ------ Input Options
% 2.31/1.00  
% 2.31/1.00  --out_options                           all
% 2.31/1.00  --tptp_safe_out                         true
% 2.31/1.00  --problem_path                          ""
% 2.31/1.00  --include_path                          ""
% 2.31/1.00  --clausifier                            res/vclausify_rel
% 2.31/1.00  --clausifier_options                    --mode clausify
% 2.31/1.00  --stdin                                 false
% 2.31/1.00  --stats_out                             all
% 2.31/1.00  
% 2.31/1.00  ------ General Options
% 2.31/1.00  
% 2.31/1.00  --fof                                   false
% 2.31/1.00  --time_out_real                         305.
% 2.31/1.00  --time_out_virtual                      -1.
% 2.31/1.00  --symbol_type_check                     false
% 2.31/1.00  --clausify_out                          false
% 2.31/1.00  --sig_cnt_out                           false
% 2.31/1.00  --trig_cnt_out                          false
% 2.31/1.00  --trig_cnt_out_tolerance                1.
% 2.31/1.00  --trig_cnt_out_sk_spl                   false
% 2.31/1.00  --abstr_cl_out                          false
% 2.31/1.00  
% 2.31/1.00  ------ Global Options
% 2.31/1.00  
% 2.31/1.00  --schedule                              default
% 2.31/1.00  --add_important_lit                     false
% 2.31/1.00  --prop_solver_per_cl                    1000
% 2.31/1.00  --min_unsat_core                        false
% 2.31/1.00  --soft_assumptions                      false
% 2.31/1.00  --soft_lemma_size                       3
% 2.31/1.00  --prop_impl_unit_size                   0
% 2.31/1.00  --prop_impl_unit                        []
% 2.31/1.00  --share_sel_clauses                     true
% 2.31/1.00  --reset_solvers                         false
% 2.31/1.00  --bc_imp_inh                            [conj_cone]
% 2.31/1.00  --conj_cone_tolerance                   3.
% 2.31/1.00  --extra_neg_conj                        none
% 2.31/1.00  --large_theory_mode                     true
% 2.31/1.00  --prolific_symb_bound                   200
% 2.31/1.00  --lt_threshold                          2000
% 2.31/1.00  --clause_weak_htbl                      true
% 2.31/1.00  --gc_record_bc_elim                     false
% 2.31/1.00  
% 2.31/1.00  ------ Preprocessing Options
% 2.31/1.00  
% 2.31/1.00  --preprocessing_flag                    true
% 2.31/1.00  --time_out_prep_mult                    0.1
% 2.31/1.00  --splitting_mode                        input
% 2.31/1.00  --splitting_grd                         true
% 2.31/1.00  --splitting_cvd                         false
% 2.31/1.00  --splitting_cvd_svl                     false
% 2.31/1.00  --splitting_nvd                         32
% 2.31/1.00  --sub_typing                            true
% 2.31/1.00  --prep_gs_sim                           true
% 2.31/1.00  --prep_unflatten                        true
% 2.31/1.00  --prep_res_sim                          true
% 2.31/1.00  --prep_upred                            true
% 2.31/1.00  --prep_sem_filter                       exhaustive
% 2.31/1.00  --prep_sem_filter_out                   false
% 2.31/1.00  --pred_elim                             true
% 2.31/1.00  --res_sim_input                         true
% 2.31/1.00  --eq_ax_congr_red                       true
% 2.31/1.00  --pure_diseq_elim                       true
% 2.31/1.00  --brand_transform                       false
% 2.31/1.00  --non_eq_to_eq                          false
% 2.31/1.00  --prep_def_merge                        true
% 2.31/1.00  --prep_def_merge_prop_impl              false
% 2.31/1.00  --prep_def_merge_mbd                    true
% 2.31/1.00  --prep_def_merge_tr_red                 false
% 2.31/1.00  --prep_def_merge_tr_cl                  false
% 2.31/1.00  --smt_preprocessing                     true
% 2.31/1.00  --smt_ac_axioms                         fast
% 2.31/1.00  --preprocessed_out                      false
% 2.31/1.00  --preprocessed_stats                    false
% 2.31/1.00  
% 2.31/1.00  ------ Abstraction refinement Options
% 2.31/1.00  
% 2.31/1.00  --abstr_ref                             []
% 2.31/1.00  --abstr_ref_prep                        false
% 2.31/1.00  --abstr_ref_until_sat                   false
% 2.31/1.00  --abstr_ref_sig_restrict                funpre
% 2.31/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.31/1.00  --abstr_ref_under                       []
% 2.31/1.00  
% 2.31/1.00  ------ SAT Options
% 2.31/1.00  
% 2.31/1.00  --sat_mode                              false
% 2.31/1.00  --sat_fm_restart_options                ""
% 2.31/1.00  --sat_gr_def                            false
% 2.31/1.00  --sat_epr_types                         true
% 2.31/1.00  --sat_non_cyclic_types                  false
% 2.31/1.00  --sat_finite_models                     false
% 2.31/1.00  --sat_fm_lemmas                         false
% 2.31/1.00  --sat_fm_prep                           false
% 2.31/1.00  --sat_fm_uc_incr                        true
% 2.31/1.00  --sat_out_model                         small
% 2.31/1.00  --sat_out_clauses                       false
% 2.31/1.00  
% 2.31/1.00  ------ QBF Options
% 2.31/1.00  
% 2.31/1.00  --qbf_mode                              false
% 2.31/1.00  --qbf_elim_univ                         false
% 2.31/1.00  --qbf_dom_inst                          none
% 2.31/1.00  --qbf_dom_pre_inst                      false
% 2.31/1.00  --qbf_sk_in                             false
% 2.31/1.00  --qbf_pred_elim                         true
% 2.31/1.00  --qbf_split                             512
% 2.31/1.00  
% 2.31/1.00  ------ BMC1 Options
% 2.31/1.00  
% 2.31/1.00  --bmc1_incremental                      false
% 2.31/1.00  --bmc1_axioms                           reachable_all
% 2.31/1.00  --bmc1_min_bound                        0
% 2.31/1.00  --bmc1_max_bound                        -1
% 2.31/1.00  --bmc1_max_bound_default                -1
% 2.31/1.00  --bmc1_symbol_reachability              true
% 2.31/1.00  --bmc1_property_lemmas                  false
% 2.31/1.00  --bmc1_k_induction                      false
% 2.31/1.00  --bmc1_non_equiv_states                 false
% 2.31/1.00  --bmc1_deadlock                         false
% 2.31/1.00  --bmc1_ucm                              false
% 2.31/1.00  --bmc1_add_unsat_core                   none
% 2.31/1.00  --bmc1_unsat_core_children              false
% 2.31/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.31/1.00  --bmc1_out_stat                         full
% 2.31/1.00  --bmc1_ground_init                      false
% 2.31/1.00  --bmc1_pre_inst_next_state              false
% 2.31/1.00  --bmc1_pre_inst_state                   false
% 2.31/1.00  --bmc1_pre_inst_reach_state             false
% 2.31/1.00  --bmc1_out_unsat_core                   false
% 2.31/1.00  --bmc1_aig_witness_out                  false
% 2.31/1.00  --bmc1_verbose                          false
% 2.31/1.00  --bmc1_dump_clauses_tptp                false
% 2.31/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.31/1.00  --bmc1_dump_file                        -
% 2.31/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.31/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.31/1.00  --bmc1_ucm_extend_mode                  1
% 2.31/1.00  --bmc1_ucm_init_mode                    2
% 2.31/1.00  --bmc1_ucm_cone_mode                    none
% 2.31/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.31/1.00  --bmc1_ucm_relax_model                  4
% 2.31/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.31/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.31/1.00  --bmc1_ucm_layered_model                none
% 2.31/1.00  --bmc1_ucm_max_lemma_size               10
% 2.31/1.00  
% 2.31/1.00  ------ AIG Options
% 2.31/1.00  
% 2.31/1.00  --aig_mode                              false
% 2.31/1.00  
% 2.31/1.00  ------ Instantiation Options
% 2.31/1.00  
% 2.31/1.00  --instantiation_flag                    true
% 2.31/1.00  --inst_sos_flag                         false
% 2.31/1.00  --inst_sos_phase                        true
% 2.31/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.31/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.31/1.00  --inst_lit_sel_side                     num_symb
% 2.31/1.00  --inst_solver_per_active                1400
% 2.31/1.00  --inst_solver_calls_frac                1.
% 2.31/1.00  --inst_passive_queue_type               priority_queues
% 2.31/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.31/1.00  --inst_passive_queues_freq              [25;2]
% 2.31/1.00  --inst_dismatching                      true
% 2.31/1.00  --inst_eager_unprocessed_to_passive     true
% 2.31/1.00  --inst_prop_sim_given                   true
% 2.31/1.00  --inst_prop_sim_new                     false
% 2.31/1.00  --inst_subs_new                         false
% 2.31/1.00  --inst_eq_res_simp                      false
% 2.31/1.00  --inst_subs_given                       false
% 2.31/1.00  --inst_orphan_elimination               true
% 2.31/1.00  --inst_learning_loop_flag               true
% 2.31/1.00  --inst_learning_start                   3000
% 2.31/1.00  --inst_learning_factor                  2
% 2.31/1.00  --inst_start_prop_sim_after_learn       3
% 2.31/1.00  --inst_sel_renew                        solver
% 2.31/1.00  --inst_lit_activity_flag                true
% 2.31/1.00  --inst_restr_to_given                   false
% 2.31/1.00  --inst_activity_threshold               500
% 2.31/1.00  --inst_out_proof                        true
% 2.31/1.00  
% 2.31/1.00  ------ Resolution Options
% 2.31/1.00  
% 2.31/1.00  --resolution_flag                       true
% 2.31/1.00  --res_lit_sel                           adaptive
% 2.31/1.00  --res_lit_sel_side                      none
% 2.31/1.00  --res_ordering                          kbo
% 2.31/1.00  --res_to_prop_solver                    active
% 2.31/1.00  --res_prop_simpl_new                    false
% 2.31/1.00  --res_prop_simpl_given                  true
% 2.31/1.00  --res_passive_queue_type                priority_queues
% 2.31/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.31/1.00  --res_passive_queues_freq               [15;5]
% 2.31/1.00  --res_forward_subs                      full
% 2.31/1.00  --res_backward_subs                     full
% 2.31/1.00  --res_forward_subs_resolution           true
% 2.31/1.00  --res_backward_subs_resolution          true
% 2.31/1.00  --res_orphan_elimination                true
% 2.31/1.00  --res_time_limit                        2.
% 2.31/1.00  --res_out_proof                         true
% 2.31/1.00  
% 2.31/1.00  ------ Superposition Options
% 2.31/1.00  
% 2.31/1.00  --superposition_flag                    true
% 2.31/1.00  --sup_passive_queue_type                priority_queues
% 2.31/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.31/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.31/1.00  --demod_completeness_check              fast
% 2.31/1.00  --demod_use_ground                      true
% 2.31/1.00  --sup_to_prop_solver                    passive
% 2.31/1.00  --sup_prop_simpl_new                    true
% 2.31/1.00  --sup_prop_simpl_given                  true
% 2.31/1.00  --sup_fun_splitting                     false
% 2.31/1.00  --sup_smt_interval                      50000
% 2.31/1.00  
% 2.31/1.00  ------ Superposition Simplification Setup
% 2.31/1.00  
% 2.31/1.00  --sup_indices_passive                   []
% 2.31/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.31/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/1.00  --sup_full_bw                           [BwDemod]
% 2.31/1.00  --sup_immed_triv                        [TrivRules]
% 2.31/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.31/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/1.00  --sup_immed_bw_main                     []
% 2.31/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.31/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/1.00  
% 2.31/1.00  ------ Combination Options
% 2.31/1.00  
% 2.31/1.00  --comb_res_mult                         3
% 2.31/1.00  --comb_sup_mult                         2
% 2.31/1.00  --comb_inst_mult                        10
% 2.31/1.00  
% 2.31/1.00  ------ Debug Options
% 2.31/1.00  
% 2.31/1.00  --dbg_backtrace                         false
% 2.31/1.00  --dbg_dump_prop_clauses                 false
% 2.31/1.00  --dbg_dump_prop_clauses_file            -
% 2.31/1.00  --dbg_out_stat                          false
% 2.31/1.00  ------ Parsing...
% 2.31/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.31/1.00  
% 2.31/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.31/1.00  
% 2.31/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.31/1.00  
% 2.31/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.31/1.00  ------ Proving...
% 2.31/1.00  ------ Problem Properties 
% 2.31/1.00  
% 2.31/1.00  
% 2.31/1.00  clauses                                 19
% 2.31/1.00  conjectures                             3
% 2.31/1.00  EPR                                     5
% 2.31/1.00  Horn                                    18
% 2.31/1.00  unary                                   5
% 2.31/1.00  binary                                  7
% 2.31/1.00  lits                                    40
% 2.31/1.00  lits eq                                 8
% 2.31/1.00  fd_pure                                 0
% 2.31/1.00  fd_pseudo                               0
% 2.31/1.00  fd_cond                                 0
% 2.31/1.00  fd_pseudo_cond                          1
% 2.31/1.00  AC symbols                              0
% 2.31/1.00  
% 2.31/1.00  ------ Schedule dynamic 5 is on 
% 2.31/1.00  
% 2.31/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.31/1.00  
% 2.31/1.00  
% 2.31/1.00  ------ 
% 2.31/1.00  Current options:
% 2.31/1.00  ------ 
% 2.31/1.00  
% 2.31/1.00  ------ Input Options
% 2.31/1.00  
% 2.31/1.00  --out_options                           all
% 2.31/1.00  --tptp_safe_out                         true
% 2.31/1.00  --problem_path                          ""
% 2.31/1.00  --include_path                          ""
% 2.31/1.00  --clausifier                            res/vclausify_rel
% 2.31/1.00  --clausifier_options                    --mode clausify
% 2.31/1.00  --stdin                                 false
% 2.31/1.00  --stats_out                             all
% 2.31/1.00  
% 2.31/1.00  ------ General Options
% 2.31/1.00  
% 2.31/1.00  --fof                                   false
% 2.31/1.00  --time_out_real                         305.
% 2.31/1.00  --time_out_virtual                      -1.
% 2.31/1.00  --symbol_type_check                     false
% 2.31/1.00  --clausify_out                          false
% 2.31/1.00  --sig_cnt_out                           false
% 2.31/1.00  --trig_cnt_out                          false
% 2.31/1.00  --trig_cnt_out_tolerance                1.
% 2.31/1.00  --trig_cnt_out_sk_spl                   false
% 2.31/1.00  --abstr_cl_out                          false
% 2.31/1.00  
% 2.31/1.00  ------ Global Options
% 2.31/1.00  
% 2.31/1.00  --schedule                              default
% 2.31/1.00  --add_important_lit                     false
% 2.31/1.00  --prop_solver_per_cl                    1000
% 2.31/1.00  --min_unsat_core                        false
% 2.31/1.00  --soft_assumptions                      false
% 2.31/1.00  --soft_lemma_size                       3
% 2.31/1.00  --prop_impl_unit_size                   0
% 2.31/1.00  --prop_impl_unit                        []
% 2.31/1.00  --share_sel_clauses                     true
% 2.31/1.00  --reset_solvers                         false
% 2.31/1.00  --bc_imp_inh                            [conj_cone]
% 2.31/1.00  --conj_cone_tolerance                   3.
% 2.31/1.00  --extra_neg_conj                        none
% 2.31/1.00  --large_theory_mode                     true
% 2.31/1.00  --prolific_symb_bound                   200
% 2.31/1.00  --lt_threshold                          2000
% 2.31/1.00  --clause_weak_htbl                      true
% 2.31/1.00  --gc_record_bc_elim                     false
% 2.31/1.00  
% 2.31/1.00  ------ Preprocessing Options
% 2.31/1.00  
% 2.31/1.00  --preprocessing_flag                    true
% 2.31/1.00  --time_out_prep_mult                    0.1
% 2.31/1.00  --splitting_mode                        input
% 2.31/1.00  --splitting_grd                         true
% 2.31/1.00  --splitting_cvd                         false
% 2.31/1.00  --splitting_cvd_svl                     false
% 2.31/1.00  --splitting_nvd                         32
% 2.31/1.00  --sub_typing                            true
% 2.31/1.00  --prep_gs_sim                           true
% 2.31/1.00  --prep_unflatten                        true
% 2.31/1.00  --prep_res_sim                          true
% 2.31/1.00  --prep_upred                            true
% 2.31/1.00  --prep_sem_filter                       exhaustive
% 2.31/1.00  --prep_sem_filter_out                   false
% 2.31/1.00  --pred_elim                             true
% 2.31/1.00  --res_sim_input                         true
% 2.31/1.00  --eq_ax_congr_red                       true
% 2.31/1.00  --pure_diseq_elim                       true
% 2.31/1.00  --brand_transform                       false
% 2.31/1.00  --non_eq_to_eq                          false
% 2.31/1.00  --prep_def_merge                        true
% 2.31/1.00  --prep_def_merge_prop_impl              false
% 2.31/1.00  --prep_def_merge_mbd                    true
% 2.31/1.00  --prep_def_merge_tr_red                 false
% 2.31/1.00  --prep_def_merge_tr_cl                  false
% 2.31/1.00  --smt_preprocessing                     true
% 2.31/1.00  --smt_ac_axioms                         fast
% 2.31/1.00  --preprocessed_out                      false
% 2.31/1.00  --preprocessed_stats                    false
% 2.31/1.00  
% 2.31/1.00  ------ Abstraction refinement Options
% 2.31/1.00  
% 2.31/1.00  --abstr_ref                             []
% 2.31/1.00  --abstr_ref_prep                        false
% 2.31/1.00  --abstr_ref_until_sat                   false
% 2.31/1.00  --abstr_ref_sig_restrict                funpre
% 2.31/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.31/1.00  --abstr_ref_under                       []
% 2.31/1.00  
% 2.31/1.00  ------ SAT Options
% 2.31/1.00  
% 2.31/1.00  --sat_mode                              false
% 2.31/1.00  --sat_fm_restart_options                ""
% 2.31/1.00  --sat_gr_def                            false
% 2.31/1.00  --sat_epr_types                         true
% 2.31/1.00  --sat_non_cyclic_types                  false
% 2.31/1.00  --sat_finite_models                     false
% 2.31/1.00  --sat_fm_lemmas                         false
% 2.31/1.00  --sat_fm_prep                           false
% 2.31/1.00  --sat_fm_uc_incr                        true
% 2.31/1.00  --sat_out_model                         small
% 2.31/1.00  --sat_out_clauses                       false
% 2.31/1.00  
% 2.31/1.00  ------ QBF Options
% 2.31/1.00  
% 2.31/1.00  --qbf_mode                              false
% 2.31/1.00  --qbf_elim_univ                         false
% 2.31/1.00  --qbf_dom_inst                          none
% 2.31/1.00  --qbf_dom_pre_inst                      false
% 2.31/1.00  --qbf_sk_in                             false
% 2.31/1.00  --qbf_pred_elim                         true
% 2.31/1.00  --qbf_split                             512
% 2.31/1.00  
% 2.31/1.00  ------ BMC1 Options
% 2.31/1.00  
% 2.31/1.00  --bmc1_incremental                      false
% 2.31/1.00  --bmc1_axioms                           reachable_all
% 2.31/1.00  --bmc1_min_bound                        0
% 2.31/1.00  --bmc1_max_bound                        -1
% 2.31/1.00  --bmc1_max_bound_default                -1
% 2.31/1.00  --bmc1_symbol_reachability              true
% 2.31/1.00  --bmc1_property_lemmas                  false
% 2.31/1.00  --bmc1_k_induction                      false
% 2.31/1.00  --bmc1_non_equiv_states                 false
% 2.31/1.00  --bmc1_deadlock                         false
% 2.31/1.00  --bmc1_ucm                              false
% 2.31/1.00  --bmc1_add_unsat_core                   none
% 2.31/1.00  --bmc1_unsat_core_children              false
% 2.31/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.31/1.00  --bmc1_out_stat                         full
% 2.31/1.00  --bmc1_ground_init                      false
% 2.31/1.00  --bmc1_pre_inst_next_state              false
% 2.31/1.00  --bmc1_pre_inst_state                   false
% 2.31/1.00  --bmc1_pre_inst_reach_state             false
% 2.31/1.00  --bmc1_out_unsat_core                   false
% 2.31/1.00  --bmc1_aig_witness_out                  false
% 2.31/1.00  --bmc1_verbose                          false
% 2.31/1.00  --bmc1_dump_clauses_tptp                false
% 2.31/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.31/1.00  --bmc1_dump_file                        -
% 2.31/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.31/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.31/1.00  --bmc1_ucm_extend_mode                  1
% 2.31/1.00  --bmc1_ucm_init_mode                    2
% 2.31/1.00  --bmc1_ucm_cone_mode                    none
% 2.31/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.31/1.00  --bmc1_ucm_relax_model                  4
% 2.31/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.31/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.31/1.00  --bmc1_ucm_layered_model                none
% 2.31/1.00  --bmc1_ucm_max_lemma_size               10
% 2.31/1.00  
% 2.31/1.00  ------ AIG Options
% 2.31/1.00  
% 2.31/1.00  --aig_mode                              false
% 2.31/1.00  
% 2.31/1.00  ------ Instantiation Options
% 2.31/1.00  
% 2.31/1.00  --instantiation_flag                    true
% 2.31/1.00  --inst_sos_flag                         false
% 2.31/1.00  --inst_sos_phase                        true
% 2.31/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.31/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.31/1.00  --inst_lit_sel_side                     none
% 2.31/1.00  --inst_solver_per_active                1400
% 2.31/1.00  --inst_solver_calls_frac                1.
% 2.31/1.00  --inst_passive_queue_type               priority_queues
% 2.31/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.31/1.00  --inst_passive_queues_freq              [25;2]
% 2.31/1.00  --inst_dismatching                      true
% 2.31/1.00  --inst_eager_unprocessed_to_passive     true
% 2.31/1.00  --inst_prop_sim_given                   true
% 2.31/1.00  --inst_prop_sim_new                     false
% 2.31/1.00  --inst_subs_new                         false
% 2.31/1.00  --inst_eq_res_simp                      false
% 2.31/1.00  --inst_subs_given                       false
% 2.31/1.00  --inst_orphan_elimination               true
% 2.31/1.00  --inst_learning_loop_flag               true
% 2.31/1.00  --inst_learning_start                   3000
% 2.31/1.00  --inst_learning_factor                  2
% 2.31/1.00  --inst_start_prop_sim_after_learn       3
% 2.31/1.00  --inst_sel_renew                        solver
% 2.31/1.00  --inst_lit_activity_flag                true
% 2.31/1.00  --inst_restr_to_given                   false
% 2.31/1.00  --inst_activity_threshold               500
% 2.31/1.00  --inst_out_proof                        true
% 2.31/1.00  
% 2.31/1.00  ------ Resolution Options
% 2.31/1.00  
% 2.31/1.00  --resolution_flag                       false
% 2.31/1.00  --res_lit_sel                           adaptive
% 2.31/1.00  --res_lit_sel_side                      none
% 2.31/1.00  --res_ordering                          kbo
% 2.31/1.00  --res_to_prop_solver                    active
% 2.31/1.00  --res_prop_simpl_new                    false
% 2.31/1.00  --res_prop_simpl_given                  true
% 2.31/1.00  --res_passive_queue_type                priority_queues
% 2.31/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.31/1.00  --res_passive_queues_freq               [15;5]
% 2.31/1.00  --res_forward_subs                      full
% 2.31/1.00  --res_backward_subs                     full
% 2.31/1.00  --res_forward_subs_resolution           true
% 2.31/1.00  --res_backward_subs_resolution          true
% 2.31/1.00  --res_orphan_elimination                true
% 2.31/1.00  --res_time_limit                        2.
% 2.31/1.00  --res_out_proof                         true
% 2.31/1.00  
% 2.31/1.00  ------ Superposition Options
% 2.31/1.00  
% 2.31/1.00  --superposition_flag                    true
% 2.31/1.00  --sup_passive_queue_type                priority_queues
% 2.31/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.31/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.31/1.00  --demod_completeness_check              fast
% 2.31/1.00  --demod_use_ground                      true
% 2.31/1.00  --sup_to_prop_solver                    passive
% 2.31/1.00  --sup_prop_simpl_new                    true
% 2.31/1.00  --sup_prop_simpl_given                  true
% 2.31/1.00  --sup_fun_splitting                     false
% 2.31/1.00  --sup_smt_interval                      50000
% 2.31/1.00  
% 2.31/1.00  ------ Superposition Simplification Setup
% 2.31/1.00  
% 2.31/1.00  --sup_indices_passive                   []
% 2.31/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.31/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.31/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/1.00  --sup_full_bw                           [BwDemod]
% 2.31/1.00  --sup_immed_triv                        [TrivRules]
% 2.31/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.31/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/1.00  --sup_immed_bw_main                     []
% 2.31/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.31/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.31/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.31/1.00  
% 2.31/1.00  ------ Combination Options
% 2.31/1.00  
% 2.31/1.00  --comb_res_mult                         3
% 2.31/1.00  --comb_sup_mult                         2
% 2.31/1.00  --comb_inst_mult                        10
% 2.31/1.00  
% 2.31/1.00  ------ Debug Options
% 2.31/1.00  
% 2.31/1.00  --dbg_backtrace                         false
% 2.31/1.00  --dbg_dump_prop_clauses                 false
% 2.31/1.00  --dbg_dump_prop_clauses_file            -
% 2.31/1.00  --dbg_out_stat                          false
% 2.31/1.00  
% 2.31/1.00  
% 2.31/1.00  
% 2.31/1.00  
% 2.31/1.00  ------ Proving...
% 2.31/1.00  
% 2.31/1.00  
% 2.31/1.00  % SZS status Theorem for theBenchmark.p
% 2.31/1.00  
% 2.31/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.31/1.00  
% 2.31/1.00  fof(f13,conjecture,(
% 2.31/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 2.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f14,negated_conjecture,(
% 2.31/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 2.31/1.00    inference(negated_conjecture,[],[f13])).
% 2.31/1.00  
% 2.31/1.00  fof(f15,plain,(
% 2.31/1.00    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))),
% 2.31/1.00    inference(pure_predicate_removal,[],[f14])).
% 2.31/1.00  
% 2.31/1.00  fof(f26,plain,(
% 2.31/1.00    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.31/1.00    inference(ennf_transformation,[],[f15])).
% 2.31/1.00  
% 2.31/1.00  fof(f27,plain,(
% 2.31/1.00    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.31/1.00    inference(flattening,[],[f26])).
% 2.31/1.00  
% 2.31/1.00  fof(f37,plain,(
% 2.31/1.00    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (! [X3] : (~r2_hidden(X3,k1_relset_1(sK2,sK1,sK3)) | ~m1_subset_1(X3,sK2)) & k1_xboole_0 != k2_relset_1(sK2,sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))))),
% 2.31/1.00    introduced(choice_axiom,[])).
% 2.31/1.00  
% 2.31/1.00  fof(f38,plain,(
% 2.31/1.00    ! [X3] : (~r2_hidden(X3,k1_relset_1(sK2,sK1,sK3)) | ~m1_subset_1(X3,sK2)) & k1_xboole_0 != k2_relset_1(sK2,sK1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.31/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f37])).
% 2.31/1.00  
% 2.31/1.00  fof(f58,plain,(
% 2.31/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.31/1.00    inference(cnf_transformation,[],[f38])).
% 2.31/1.00  
% 2.31/1.00  fof(f10,axiom,(
% 2.31/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f16,plain,(
% 2.31/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.31/1.00    inference(pure_predicate_removal,[],[f10])).
% 2.31/1.00  
% 2.31/1.00  fof(f23,plain,(
% 2.31/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.31/1.00    inference(ennf_transformation,[],[f16])).
% 2.31/1.00  
% 2.31/1.00  fof(f55,plain,(
% 2.31/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.31/1.00    inference(cnf_transformation,[],[f23])).
% 2.31/1.00  
% 2.31/1.00  fof(f7,axiom,(
% 2.31/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f21,plain,(
% 2.31/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.31/1.00    inference(ennf_transformation,[],[f7])).
% 2.31/1.00  
% 2.31/1.00  fof(f35,plain,(
% 2.31/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.31/1.00    inference(nnf_transformation,[],[f21])).
% 2.31/1.00  
% 2.31/1.00  fof(f50,plain,(
% 2.31/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.31/1.00    inference(cnf_transformation,[],[f35])).
% 2.31/1.00  
% 2.31/1.00  fof(f1,axiom,(
% 2.31/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f17,plain,(
% 2.31/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.31/1.00    inference(ennf_transformation,[],[f1])).
% 2.31/1.00  
% 2.31/1.00  fof(f28,plain,(
% 2.31/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.31/1.00    inference(nnf_transformation,[],[f17])).
% 2.31/1.00  
% 2.31/1.00  fof(f29,plain,(
% 2.31/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.31/1.00    inference(rectify,[],[f28])).
% 2.31/1.00  
% 2.31/1.00  fof(f30,plain,(
% 2.31/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.31/1.00    introduced(choice_axiom,[])).
% 2.31/1.00  
% 2.31/1.00  fof(f31,plain,(
% 2.31/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.31/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).
% 2.31/1.00  
% 2.31/1.00  fof(f40,plain,(
% 2.31/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.31/1.00    inference(cnf_transformation,[],[f31])).
% 2.31/1.00  
% 2.31/1.00  fof(f39,plain,(
% 2.31/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.31/1.00    inference(cnf_transformation,[],[f31])).
% 2.31/1.00  
% 2.31/1.00  fof(f4,axiom,(
% 2.31/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f34,plain,(
% 2.31/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.31/1.00    inference(nnf_transformation,[],[f4])).
% 2.31/1.00  
% 2.31/1.00  fof(f46,plain,(
% 2.31/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.31/1.00    inference(cnf_transformation,[],[f34])).
% 2.31/1.00  
% 2.31/1.00  fof(f6,axiom,(
% 2.31/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f20,plain,(
% 2.31/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.31/1.00    inference(ennf_transformation,[],[f6])).
% 2.31/1.00  
% 2.31/1.00  fof(f49,plain,(
% 2.31/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.31/1.00    inference(cnf_transformation,[],[f20])).
% 2.31/1.00  
% 2.31/1.00  fof(f47,plain,(
% 2.31/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.31/1.00    inference(cnf_transformation,[],[f34])).
% 2.31/1.00  
% 2.31/1.00  fof(f8,axiom,(
% 2.31/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f52,plain,(
% 2.31/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.31/1.00    inference(cnf_transformation,[],[f8])).
% 2.31/1.00  
% 2.31/1.00  fof(f5,axiom,(
% 2.31/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f18,plain,(
% 2.31/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.31/1.00    inference(ennf_transformation,[],[f5])).
% 2.31/1.00  
% 2.31/1.00  fof(f19,plain,(
% 2.31/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.31/1.00    inference(flattening,[],[f18])).
% 2.31/1.00  
% 2.31/1.00  fof(f48,plain,(
% 2.31/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.31/1.00    inference(cnf_transformation,[],[f19])).
% 2.31/1.00  
% 2.31/1.00  fof(f11,axiom,(
% 2.31/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f24,plain,(
% 2.31/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.31/1.00    inference(ennf_transformation,[],[f11])).
% 2.31/1.00  
% 2.31/1.00  fof(f56,plain,(
% 2.31/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.31/1.00    inference(cnf_transformation,[],[f24])).
% 2.31/1.00  
% 2.31/1.00  fof(f60,plain,(
% 2.31/1.00    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK2,sK1,sK3)) | ~m1_subset_1(X3,sK2)) )),
% 2.31/1.00    inference(cnf_transformation,[],[f38])).
% 2.31/1.00  
% 2.31/1.00  fof(f3,axiom,(
% 2.31/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f45,plain,(
% 2.31/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.31/1.00    inference(cnf_transformation,[],[f3])).
% 2.31/1.00  
% 2.31/1.00  fof(f2,axiom,(
% 2.31/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f32,plain,(
% 2.31/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.31/1.00    inference(nnf_transformation,[],[f2])).
% 2.31/1.00  
% 2.31/1.00  fof(f33,plain,(
% 2.31/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.31/1.00    inference(flattening,[],[f32])).
% 2.31/1.00  
% 2.31/1.00  fof(f44,plain,(
% 2.31/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.31/1.00    inference(cnf_transformation,[],[f33])).
% 2.31/1.00  
% 2.31/1.00  fof(f9,axiom,(
% 2.31/1.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f22,plain,(
% 2.31/1.00    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.31/1.00    inference(ennf_transformation,[],[f9])).
% 2.31/1.00  
% 2.31/1.00  fof(f36,plain,(
% 2.31/1.00    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.31/1.00    inference(nnf_transformation,[],[f22])).
% 2.31/1.00  
% 2.31/1.00  fof(f53,plain,(
% 2.31/1.00    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.31/1.00    inference(cnf_transformation,[],[f36])).
% 2.31/1.00  
% 2.31/1.00  fof(f12,axiom,(
% 2.31/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.31/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.31/1.00  
% 2.31/1.00  fof(f25,plain,(
% 2.31/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.31/1.00    inference(ennf_transformation,[],[f12])).
% 2.31/1.00  
% 2.31/1.00  fof(f57,plain,(
% 2.31/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.31/1.00    inference(cnf_transformation,[],[f25])).
% 2.31/1.00  
% 2.31/1.00  fof(f59,plain,(
% 2.31/1.00    k1_xboole_0 != k2_relset_1(sK2,sK1,sK3)),
% 2.31/1.00    inference(cnf_transformation,[],[f38])).
% 2.31/1.00  
% 2.31/1.00  cnf(c_21,negated_conjecture,
% 2.31/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 2.31/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_912,plain,
% 2.31/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 2.31/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_16,plain,
% 2.31/1.00      ( v4_relat_1(X0,X1)
% 2.31/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.31/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_12,plain,
% 2.31/1.00      ( ~ v4_relat_1(X0,X1)
% 2.31/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 2.31/1.00      | ~ v1_relat_1(X0) ),
% 2.31/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_275,plain,
% 2.31/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.31/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 2.31/1.00      | ~ v1_relat_1(X0) ),
% 2.31/1.00      inference(resolution,[status(thm)],[c_16,c_12]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_910,plain,
% 2.31/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.31/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 2.31/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.31/1.00      inference(predicate_to_equality,[status(thm)],[c_275]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1283,plain,
% 2.31/1.00      ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top
% 2.31/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.31/1.00      inference(superposition,[status(thm)],[c_912,c_910]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1,plain,
% 2.31/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.31/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_926,plain,
% 2.31/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.31/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.31/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_2,plain,
% 2.31/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.31/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_925,plain,
% 2.31/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.31/1.00      | r2_hidden(X0,X2) = iProver_top
% 2.31/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 2.31/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1920,plain,
% 2.31/1.00      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 2.31/1.00      | r1_tarski(X0,X2) != iProver_top
% 2.31/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.31/1.00      inference(superposition,[status(thm)],[c_926,c_925]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_3347,plain,
% 2.31/1.00      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 2.31/1.00      | r1_tarski(X0,X3) != iProver_top
% 2.31/1.00      | r1_tarski(X3,X2) != iProver_top
% 2.31/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.31/1.00      inference(superposition,[status(thm)],[c_1920,c_925]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_4714,plain,
% 2.31/1.00      ( r2_hidden(sK0(k1_relat_1(sK3),X0),X1) = iProver_top
% 2.31/1.00      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.31/1.00      | r1_tarski(sK2,X1) != iProver_top
% 2.31/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.31/1.00      inference(superposition,[status(thm)],[c_1283,c_3347]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_8,plain,
% 2.31/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.31/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_920,plain,
% 2.31/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.31/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.31/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1226,plain,
% 2.31/1.00      ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK1)) = iProver_top ),
% 2.31/1.00      inference(superposition,[status(thm)],[c_912,c_920]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_10,plain,
% 2.31/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.31/1.00      | ~ v1_relat_1(X1)
% 2.31/1.00      | v1_relat_1(X0) ),
% 2.31/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_7,plain,
% 2.31/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.31/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_164,plain,
% 2.31/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.31/1.00      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_165,plain,
% 2.31/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.31/1.00      inference(renaming,[status(thm)],[c_164]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_203,plain,
% 2.31/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.31/1.00      inference(bin_hyper_res,[status(thm)],[c_10,c_165]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_911,plain,
% 2.31/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.31/1.00      | v1_relat_1(X1) != iProver_top
% 2.31/1.00      | v1_relat_1(X0) = iProver_top ),
% 2.31/1.00      inference(predicate_to_equality,[status(thm)],[c_203]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1625,plain,
% 2.31/1.00      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 2.31/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.31/1.00      inference(superposition,[status(thm)],[c_1226,c_911]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_13,plain,
% 2.31/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.31/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_918,plain,
% 2.31/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.31/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1647,plain,
% 2.31/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 2.31/1.00      inference(forward_subsumption_resolution,
% 2.31/1.00                [status(thm)],
% 2.31/1.00                [c_1625,c_918]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_921,plain,
% 2.31/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.31/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.31/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_9,plain,
% 2.31/1.00      ( m1_subset_1(X0,X1)
% 2.31/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.31/1.00      | ~ r2_hidden(X0,X2) ),
% 2.31/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_919,plain,
% 2.31/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 2.31/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.31/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 2.31/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1942,plain,
% 2.31/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 2.31/1.00      | r2_hidden(X0,X2) != iProver_top
% 2.31/1.00      | r1_tarski(X2,X1) != iProver_top ),
% 2.31/1.00      inference(superposition,[status(thm)],[c_921,c_919]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_3691,plain,
% 2.31/1.00      ( m1_subset_1(sK0(X0,X1),X2) = iProver_top
% 2.31/1.00      | r1_tarski(X0,X2) != iProver_top
% 2.31/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.31/1.00      inference(superposition,[status(thm)],[c_926,c_1942]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_17,plain,
% 2.31/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.31/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.31/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_915,plain,
% 2.31/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.31/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.31/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1811,plain,
% 2.31/1.00      ( k1_relset_1(sK2,sK1,sK3) = k1_relat_1(sK3) ),
% 2.31/1.00      inference(superposition,[status(thm)],[c_912,c_915]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_19,negated_conjecture,
% 2.31/1.00      ( ~ m1_subset_1(X0,sK2)
% 2.31/1.00      | ~ r2_hidden(X0,k1_relset_1(sK2,sK1,sK3)) ),
% 2.31/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_913,plain,
% 2.31/1.00      ( m1_subset_1(X0,sK2) != iProver_top
% 2.31/1.00      | r2_hidden(X0,k1_relset_1(sK2,sK1,sK3)) != iProver_top ),
% 2.31/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1377,plain,
% 2.31/1.00      ( m1_subset_1(sK0(k1_relset_1(sK2,sK1,sK3),X0),sK2) != iProver_top
% 2.31/1.00      | r1_tarski(k1_relset_1(sK2,sK1,sK3),X0) = iProver_top ),
% 2.31/1.00      inference(superposition,[status(thm)],[c_926,c_913]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_2110,plain,
% 2.31/1.00      ( m1_subset_1(sK0(k1_relat_1(sK3),X0),sK2) != iProver_top
% 2.31/1.00      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 2.31/1.00      inference(demodulation,[status(thm)],[c_1811,c_1377]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_4762,plain,
% 2.31/1.00      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.31/1.00      | r1_tarski(k1_relat_1(sK3),sK2) != iProver_top ),
% 2.31/1.00      inference(superposition,[status(thm)],[c_3691,c_2110]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_5320,plain,
% 2.31/1.00      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 2.31/1.00      inference(global_propositional_subsumption,
% 2.31/1.00                [status(thm)],
% 2.31/1.00                [c_4714,c_1283,c_1647,c_4762]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_6,plain,
% 2.31/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.31/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_922,plain,
% 2.31/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.31/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_3,plain,
% 2.31/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.31/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_924,plain,
% 2.31/1.00      ( X0 = X1
% 2.31/1.00      | r1_tarski(X1,X0) != iProver_top
% 2.31/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.31/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1896,plain,
% 2.31/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.31/1.00      inference(superposition,[status(thm)],[c_922,c_924]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_5330,plain,
% 2.31/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.31/1.00      inference(superposition,[status(thm)],[c_5320,c_1896]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_15,plain,
% 2.31/1.00      ( ~ v1_relat_1(X0)
% 2.31/1.00      | k2_relat_1(X0) = k1_xboole_0
% 2.31/1.00      | k1_relat_1(X0) != k1_xboole_0 ),
% 2.31/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_2767,plain,
% 2.31/1.00      ( ~ v1_relat_1(sK3)
% 2.31/1.00      | k2_relat_1(sK3) = k1_xboole_0
% 2.31/1.00      | k1_relat_1(sK3) != k1_xboole_0 ),
% 2.31/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1648,plain,
% 2.31/1.00      ( v1_relat_1(sK3) ),
% 2.31/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1647]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_460,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1233,plain,
% 2.31/1.00      ( k2_relat_1(sK3) != X0
% 2.31/1.00      | k1_xboole_0 != X0
% 2.31/1.00      | k1_xboole_0 = k2_relat_1(sK3) ),
% 2.31/1.00      inference(instantiation,[status(thm)],[c_460]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1234,plain,
% 2.31/1.00      ( k2_relat_1(sK3) != k1_xboole_0
% 2.31/1.00      | k1_xboole_0 = k2_relat_1(sK3)
% 2.31/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.31/1.00      inference(instantiation,[status(thm)],[c_1233]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1074,plain,
% 2.31/1.00      ( k2_relset_1(sK2,sK1,sK3) != X0
% 2.31/1.00      | k1_xboole_0 != X0
% 2.31/1.00      | k1_xboole_0 = k2_relset_1(sK2,sK1,sK3) ),
% 2.31/1.00      inference(instantiation,[status(thm)],[c_460]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1133,plain,
% 2.31/1.00      ( k2_relset_1(sK2,sK1,sK3) != k2_relat_1(sK3)
% 2.31/1.00      | k1_xboole_0 = k2_relset_1(sK2,sK1,sK3)
% 2.31/1.00      | k1_xboole_0 != k2_relat_1(sK3) ),
% 2.31/1.00      inference(instantiation,[status(thm)],[c_1074]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_18,plain,
% 2.31/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.31/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.31/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_1090,plain,
% 2.31/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 2.31/1.00      | k2_relset_1(sK2,sK1,sK3) = k2_relat_1(sK3) ),
% 2.31/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_66,plain,
% 2.31/1.00      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.31/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 2.31/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_61,plain,
% 2.31/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.31/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(c_20,negated_conjecture,
% 2.31/1.00      ( k1_xboole_0 != k2_relset_1(sK2,sK1,sK3) ),
% 2.31/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.31/1.00  
% 2.31/1.00  cnf(contradiction,plain,
% 2.31/1.00      ( $false ),
% 2.31/1.00      inference(minisat,
% 2.31/1.00                [status(thm)],
% 2.31/1.00                [c_5330,c_2767,c_1648,c_1234,c_1133,c_1090,c_66,c_61,
% 2.31/1.00                 c_20,c_21]) ).
% 2.31/1.00  
% 2.31/1.00  
% 2.31/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.31/1.00  
% 2.31/1.00  ------                               Statistics
% 2.31/1.00  
% 2.31/1.00  ------ General
% 2.31/1.00  
% 2.31/1.00  abstr_ref_over_cycles:                  0
% 2.31/1.00  abstr_ref_under_cycles:                 0
% 2.31/1.00  gc_basic_clause_elim:                   0
% 2.31/1.00  forced_gc_time:                         0
% 2.31/1.00  parsing_time:                           0.009
% 2.31/1.00  unif_index_cands_time:                  0.
% 2.31/1.00  unif_index_add_time:                    0.
% 2.31/1.00  orderings_time:                         0.
% 2.31/1.00  out_proof_time:                         0.008
% 2.31/1.00  total_time:                             0.17
% 2.31/1.00  num_of_symbols:                         47
% 2.31/1.00  num_of_terms:                           5248
% 2.31/1.00  
% 2.31/1.00  ------ Preprocessing
% 2.31/1.00  
% 2.31/1.00  num_of_splits:                          0
% 2.31/1.00  num_of_split_atoms:                     0
% 2.31/1.00  num_of_reused_defs:                     0
% 2.31/1.00  num_eq_ax_congr_red:                    17
% 2.31/1.00  num_of_sem_filtered_clauses:            1
% 2.31/1.00  num_of_subtypes:                        0
% 2.31/1.00  monotx_restored_types:                  0
% 2.31/1.00  sat_num_of_epr_types:                   0
% 2.31/1.00  sat_num_of_non_cyclic_types:            0
% 2.31/1.00  sat_guarded_non_collapsed_types:        0
% 2.31/1.00  num_pure_diseq_elim:                    0
% 2.31/1.00  simp_replaced_by:                       0
% 2.31/1.00  res_preprocessed:                       99
% 2.31/1.00  prep_upred:                             0
% 2.31/1.00  prep_unflattend:                        0
% 2.31/1.00  smt_new_axioms:                         0
% 2.31/1.00  pred_elim_cands:                        4
% 2.31/1.00  pred_elim:                              1
% 2.31/1.00  pred_elim_cl:                           2
% 2.31/1.00  pred_elim_cycles:                       3
% 2.31/1.00  merged_defs:                            8
% 2.31/1.00  merged_defs_ncl:                        0
% 2.31/1.00  bin_hyper_res:                          9
% 2.31/1.00  prep_cycles:                            4
% 2.31/1.00  pred_elim_time:                         0.001
% 2.31/1.00  splitting_time:                         0.
% 2.31/1.00  sem_filter_time:                        0.
% 2.31/1.00  monotx_time:                            0.001
% 2.31/1.00  subtype_inf_time:                       0.
% 2.31/1.00  
% 2.31/1.00  ------ Problem properties
% 2.31/1.00  
% 2.31/1.00  clauses:                                19
% 2.31/1.00  conjectures:                            3
% 2.31/1.00  epr:                                    5
% 2.31/1.00  horn:                                   18
% 2.31/1.00  ground:                                 2
% 2.31/1.00  unary:                                  5
% 2.31/1.00  binary:                                 7
% 2.31/1.00  lits:                                   40
% 2.31/1.00  lits_eq:                                8
% 2.31/1.00  fd_pure:                                0
% 2.31/1.00  fd_pseudo:                              0
% 2.31/1.00  fd_cond:                                0
% 2.31/1.00  fd_pseudo_cond:                         1
% 2.31/1.00  ac_symbols:                             0
% 2.31/1.00  
% 2.31/1.00  ------ Propositional Solver
% 2.31/1.00  
% 2.31/1.00  prop_solver_calls:                      28
% 2.31/1.00  prop_fast_solver_calls:                 608
% 2.31/1.00  smt_solver_calls:                       0
% 2.31/1.00  smt_fast_solver_calls:                  0
% 2.31/1.00  prop_num_of_clauses:                    1923
% 2.31/1.00  prop_preprocess_simplified:             6436
% 2.31/1.00  prop_fo_subsumed:                       11
% 2.31/1.00  prop_solver_time:                       0.
% 2.31/1.00  smt_solver_time:                        0.
% 2.31/1.00  smt_fast_solver_time:                   0.
% 2.31/1.00  prop_fast_solver_time:                  0.
% 2.31/1.00  prop_unsat_core_time:                   0.
% 2.31/1.00  
% 2.31/1.00  ------ QBF
% 2.31/1.00  
% 2.31/1.00  qbf_q_res:                              0
% 2.31/1.00  qbf_num_tautologies:                    0
% 2.31/1.00  qbf_prep_cycles:                        0
% 2.31/1.00  
% 2.31/1.00  ------ BMC1
% 2.31/1.00  
% 2.31/1.00  bmc1_current_bound:                     -1
% 2.31/1.00  bmc1_last_solved_bound:                 -1
% 2.31/1.00  bmc1_unsat_core_size:                   -1
% 2.31/1.00  bmc1_unsat_core_parents_size:           -1
% 2.31/1.00  bmc1_merge_next_fun:                    0
% 2.31/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.31/1.00  
% 2.31/1.00  ------ Instantiation
% 2.31/1.00  
% 2.31/1.00  inst_num_of_clauses:                    593
% 2.31/1.00  inst_num_in_passive:                    250
% 2.31/1.00  inst_num_in_active:                     278
% 2.31/1.00  inst_num_in_unprocessed:                65
% 2.31/1.00  inst_num_of_loops:                      320
% 2.31/1.00  inst_num_of_learning_restarts:          0
% 2.31/1.00  inst_num_moves_active_passive:          40
% 2.31/1.00  inst_lit_activity:                      0
% 2.31/1.00  inst_lit_activity_moves:                0
% 2.31/1.00  inst_num_tautologies:                   0
% 2.31/1.00  inst_num_prop_implied:                  0
% 2.31/1.00  inst_num_existing_simplified:           0
% 2.31/1.00  inst_num_eq_res_simplified:             0
% 2.31/1.00  inst_num_child_elim:                    0
% 2.31/1.00  inst_num_of_dismatching_blockings:      117
% 2.31/1.00  inst_num_of_non_proper_insts:           570
% 2.31/1.00  inst_num_of_duplicates:                 0
% 2.31/1.00  inst_inst_num_from_inst_to_res:         0
% 2.31/1.00  inst_dismatching_checking_time:         0.
% 2.31/1.00  
% 2.31/1.00  ------ Resolution
% 2.31/1.00  
% 2.31/1.00  res_num_of_clauses:                     0
% 2.31/1.00  res_num_in_passive:                     0
% 2.31/1.00  res_num_in_active:                      0
% 2.31/1.00  res_num_of_loops:                       103
% 2.31/1.00  res_forward_subset_subsumed:            41
% 2.31/1.00  res_backward_subset_subsumed:           0
% 2.31/1.00  res_forward_subsumed:                   0
% 2.31/1.00  res_backward_subsumed:                  0
% 2.31/1.00  res_forward_subsumption_resolution:     0
% 2.31/1.00  res_backward_subsumption_resolution:    0
% 2.31/1.00  res_clause_to_clause_subsumption:       316
% 2.31/1.00  res_orphan_elimination:                 0
% 2.31/1.00  res_tautology_del:                      86
% 2.31/1.00  res_num_eq_res_simplified:              0
% 2.31/1.00  res_num_sel_changes:                    0
% 2.31/1.00  res_moves_from_active_to_pass:          0
% 2.31/1.00  
% 2.31/1.00  ------ Superposition
% 2.31/1.00  
% 2.31/1.00  sup_time_total:                         0.
% 2.31/1.00  sup_time_generating:                    0.
% 2.31/1.00  sup_time_sim_full:                      0.
% 2.31/1.00  sup_time_sim_immed:                     0.
% 2.31/1.00  
% 2.31/1.00  sup_num_of_clauses:                     92
% 2.31/1.00  sup_num_in_active:                      58
% 2.31/1.00  sup_num_in_passive:                     34
% 2.31/1.00  sup_num_of_loops:                       62
% 2.31/1.00  sup_fw_superposition:                   46
% 2.31/1.00  sup_bw_superposition:                   61
% 2.31/1.00  sup_immediate_simplified:               8
% 2.31/1.00  sup_given_eliminated:                   2
% 2.31/1.00  comparisons_done:                       0
% 2.31/1.00  comparisons_avoided:                    0
% 2.31/1.00  
% 2.31/1.00  ------ Simplifications
% 2.31/1.00  
% 2.31/1.00  
% 2.31/1.00  sim_fw_subset_subsumed:                 6
% 2.31/1.00  sim_bw_subset_subsumed:                 1
% 2.31/1.00  sim_fw_subsumed:                        3
% 2.31/1.00  sim_bw_subsumed:                        0
% 2.31/1.00  sim_fw_subsumption_res:                 2
% 2.31/1.00  sim_bw_subsumption_res:                 0
% 2.31/1.00  sim_tautology_del:                      3
% 2.31/1.00  sim_eq_tautology_del:                   2
% 2.31/1.00  sim_eq_res_simp:                        0
% 2.31/1.00  sim_fw_demodulated:                     1
% 2.31/1.00  sim_bw_demodulated:                     9
% 2.31/1.00  sim_light_normalised:                   4
% 2.31/1.00  sim_joinable_taut:                      0
% 2.31/1.00  sim_joinable_simp:                      0
% 2.31/1.00  sim_ac_normalised:                      0
% 2.31/1.00  sim_smt_subsumption:                    0
% 2.31/1.00  
%------------------------------------------------------------------------------
