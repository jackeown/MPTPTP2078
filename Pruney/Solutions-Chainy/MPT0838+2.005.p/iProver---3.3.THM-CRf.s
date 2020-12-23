%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:26 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 776 expanded)
%              Number of clauses        :   77 ( 281 expanded)
%              Number of leaves         :   21 ( 189 expanded)
%              Depth                    :   21
%              Number of atoms          :  346 (2824 expanded)
%              Number of equality atoms :  107 ( 556 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f43,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK1,sK2,sK3))
        | ~ m1_subset_1(X3,sK2) )
    & k1_xboole_0 != k1_relset_1(sK1,sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f42,f41,f40])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f30])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f45,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK1,sK2,sK3))
      | ~ m1_subset_1(X3,sK2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    k1_xboole_0 != k1_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1141,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1133,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_17,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1134,plain,
    ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2253,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1133,c_1134])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1138,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2396,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2253,c_1138])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1135,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2039,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1133,c_1135])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_336,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | v1_xboole_0(X3)
    | X2 != X3
    | sK0(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X0),X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_521,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_552,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(sK0(X0),X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_337,c_521])).

cnf(c_1127,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(sK0(X0),X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_18,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,sK2)
    | v1_xboole_0(X1)
    | k2_relset_1(sK1,sK2,sK3) != X1
    | sK0(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_365,plain,
    ( ~ m1_subset_1(sK0(k2_relset_1(sK1,sK2,sK3)),sK2)
    | v1_xboole_0(k2_relset_1(sK1,sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_1128,plain,
    ( m1_subset_1(sK0(k2_relset_1(sK1,sK2,sK3)),sK2) != iProver_top
    | v1_xboole_0(k2_relset_1(sK1,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_1480,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2) != iProver_top
    | v1_xboole_0(k2_relset_1(sK1,sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1127,c_1128])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_314,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_14,c_11])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_324,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_314,c_13])).

cnf(c_1265,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_1266,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1265])).

cnf(c_1298,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_730,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1342,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
    | k2_relset_1(sK1,sK2,sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_1427,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_1428,plain,
    ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
    | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1427])).

cnf(c_1731,plain,
    ( v1_xboole_0(k2_relset_1(sK1,sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1480,c_20,c_25,c_1266,c_1298,c_1428])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1142,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1736,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1731,c_1142])).

cnf(c_2051,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2039,c_1736])).

cnf(c_2516,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,X0)) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2396,c_2051])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_167,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_207,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_167])).

cnf(c_351,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_207])).

cnf(c_352,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_1129,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_2520,plain,
    ( r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK1,X0)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2516,c_1129])).

cnf(c_3656,plain,
    ( r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_2520])).

cnf(c_1738,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1736,c_1731])).

cnf(c_1560,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_1142])).

cnf(c_3010,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1738,c_1560])).

cnf(c_2418,plain,
    ( r1_tarski(k1_xboole_0,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2051,c_2253])).

cnf(c_3328,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3010,c_2418])).

cnf(c_5,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1140,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1151,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1140,c_4])).

cnf(c_1567,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_1138])).

cnf(c_3494,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3328,c_1567])).

cnf(c_3496,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3494,c_1138])).

cnf(c_3737,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3496,c_1129])).

cnf(c_4999,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3656,c_1738,c_3737])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1137,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1485,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_1142])).

cnf(c_5006,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4999,c_1485])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1136,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2224,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1133,c_1136])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k1_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2338,plain,
    ( k1_relat_1(sK3) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2224,c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5006,c_2338])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:57:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.53/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.01  
% 2.53/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.53/1.01  
% 2.53/1.01  ------  iProver source info
% 2.53/1.01  
% 2.53/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.53/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.53/1.01  git: non_committed_changes: false
% 2.53/1.01  git: last_make_outside_of_git: false
% 2.53/1.01  
% 2.53/1.01  ------ 
% 2.53/1.01  
% 2.53/1.01  ------ Input Options
% 2.53/1.01  
% 2.53/1.01  --out_options                           all
% 2.53/1.01  --tptp_safe_out                         true
% 2.53/1.01  --problem_path                          ""
% 2.53/1.01  --include_path                          ""
% 2.53/1.01  --clausifier                            res/vclausify_rel
% 2.53/1.01  --clausifier_options                    --mode clausify
% 2.53/1.01  --stdin                                 false
% 2.53/1.01  --stats_out                             all
% 2.53/1.01  
% 2.53/1.01  ------ General Options
% 2.53/1.01  
% 2.53/1.01  --fof                                   false
% 2.53/1.01  --time_out_real                         305.
% 2.53/1.01  --time_out_virtual                      -1.
% 2.53/1.01  --symbol_type_check                     false
% 2.53/1.01  --clausify_out                          false
% 2.53/1.01  --sig_cnt_out                           false
% 2.53/1.01  --trig_cnt_out                          false
% 2.53/1.01  --trig_cnt_out_tolerance                1.
% 2.53/1.01  --trig_cnt_out_sk_spl                   false
% 2.53/1.01  --abstr_cl_out                          false
% 2.53/1.01  
% 2.53/1.01  ------ Global Options
% 2.53/1.01  
% 2.53/1.01  --schedule                              default
% 2.53/1.01  --add_important_lit                     false
% 2.53/1.01  --prop_solver_per_cl                    1000
% 2.53/1.01  --min_unsat_core                        false
% 2.53/1.01  --soft_assumptions                      false
% 2.53/1.01  --soft_lemma_size                       3
% 2.53/1.01  --prop_impl_unit_size                   0
% 2.53/1.01  --prop_impl_unit                        []
% 2.53/1.01  --share_sel_clauses                     true
% 2.53/1.01  --reset_solvers                         false
% 2.53/1.01  --bc_imp_inh                            [conj_cone]
% 2.53/1.01  --conj_cone_tolerance                   3.
% 2.53/1.01  --extra_neg_conj                        none
% 2.53/1.01  --large_theory_mode                     true
% 2.53/1.01  --prolific_symb_bound                   200
% 2.53/1.01  --lt_threshold                          2000
% 2.53/1.01  --clause_weak_htbl                      true
% 2.53/1.01  --gc_record_bc_elim                     false
% 2.53/1.01  
% 2.53/1.01  ------ Preprocessing Options
% 2.53/1.01  
% 2.53/1.01  --preprocessing_flag                    true
% 2.53/1.01  --time_out_prep_mult                    0.1
% 2.53/1.01  --splitting_mode                        input
% 2.53/1.01  --splitting_grd                         true
% 2.53/1.01  --splitting_cvd                         false
% 2.53/1.01  --splitting_cvd_svl                     false
% 2.53/1.01  --splitting_nvd                         32
% 2.53/1.01  --sub_typing                            true
% 2.53/1.01  --prep_gs_sim                           true
% 2.53/1.01  --prep_unflatten                        true
% 2.53/1.01  --prep_res_sim                          true
% 2.53/1.01  --prep_upred                            true
% 2.53/1.01  --prep_sem_filter                       exhaustive
% 2.53/1.01  --prep_sem_filter_out                   false
% 2.53/1.01  --pred_elim                             true
% 2.53/1.01  --res_sim_input                         true
% 2.53/1.01  --eq_ax_congr_red                       true
% 2.53/1.01  --pure_diseq_elim                       true
% 2.53/1.01  --brand_transform                       false
% 2.53/1.01  --non_eq_to_eq                          false
% 2.53/1.01  --prep_def_merge                        true
% 2.53/1.01  --prep_def_merge_prop_impl              false
% 2.53/1.01  --prep_def_merge_mbd                    true
% 2.53/1.01  --prep_def_merge_tr_red                 false
% 2.53/1.01  --prep_def_merge_tr_cl                  false
% 2.53/1.01  --smt_preprocessing                     true
% 2.53/1.01  --smt_ac_axioms                         fast
% 2.53/1.01  --preprocessed_out                      false
% 2.53/1.01  --preprocessed_stats                    false
% 2.53/1.01  
% 2.53/1.01  ------ Abstraction refinement Options
% 2.53/1.01  
% 2.53/1.01  --abstr_ref                             []
% 2.53/1.01  --abstr_ref_prep                        false
% 2.53/1.01  --abstr_ref_until_sat                   false
% 2.53/1.01  --abstr_ref_sig_restrict                funpre
% 2.53/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.01  --abstr_ref_under                       []
% 2.53/1.01  
% 2.53/1.01  ------ SAT Options
% 2.53/1.01  
% 2.53/1.01  --sat_mode                              false
% 2.53/1.01  --sat_fm_restart_options                ""
% 2.53/1.01  --sat_gr_def                            false
% 2.53/1.01  --sat_epr_types                         true
% 2.53/1.01  --sat_non_cyclic_types                  false
% 2.53/1.01  --sat_finite_models                     false
% 2.53/1.01  --sat_fm_lemmas                         false
% 2.53/1.01  --sat_fm_prep                           false
% 2.53/1.01  --sat_fm_uc_incr                        true
% 2.53/1.01  --sat_out_model                         small
% 2.53/1.01  --sat_out_clauses                       false
% 2.53/1.01  
% 2.53/1.01  ------ QBF Options
% 2.53/1.01  
% 2.53/1.01  --qbf_mode                              false
% 2.53/1.01  --qbf_elim_univ                         false
% 2.53/1.01  --qbf_dom_inst                          none
% 2.53/1.01  --qbf_dom_pre_inst                      false
% 2.53/1.01  --qbf_sk_in                             false
% 2.53/1.01  --qbf_pred_elim                         true
% 2.53/1.01  --qbf_split                             512
% 2.53/1.01  
% 2.53/1.01  ------ BMC1 Options
% 2.53/1.01  
% 2.53/1.01  --bmc1_incremental                      false
% 2.53/1.01  --bmc1_axioms                           reachable_all
% 2.53/1.01  --bmc1_min_bound                        0
% 2.53/1.01  --bmc1_max_bound                        -1
% 2.53/1.01  --bmc1_max_bound_default                -1
% 2.53/1.01  --bmc1_symbol_reachability              true
% 2.53/1.01  --bmc1_property_lemmas                  false
% 2.53/1.01  --bmc1_k_induction                      false
% 2.53/1.01  --bmc1_non_equiv_states                 false
% 2.53/1.01  --bmc1_deadlock                         false
% 2.53/1.01  --bmc1_ucm                              false
% 2.53/1.01  --bmc1_add_unsat_core                   none
% 2.53/1.01  --bmc1_unsat_core_children              false
% 2.53/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.01  --bmc1_out_stat                         full
% 2.53/1.01  --bmc1_ground_init                      false
% 2.53/1.01  --bmc1_pre_inst_next_state              false
% 2.53/1.01  --bmc1_pre_inst_state                   false
% 2.53/1.01  --bmc1_pre_inst_reach_state             false
% 2.53/1.01  --bmc1_out_unsat_core                   false
% 2.53/1.01  --bmc1_aig_witness_out                  false
% 2.53/1.01  --bmc1_verbose                          false
% 2.53/1.01  --bmc1_dump_clauses_tptp                false
% 2.53/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.01  --bmc1_dump_file                        -
% 2.53/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.01  --bmc1_ucm_extend_mode                  1
% 2.53/1.01  --bmc1_ucm_init_mode                    2
% 2.53/1.01  --bmc1_ucm_cone_mode                    none
% 2.53/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.01  --bmc1_ucm_relax_model                  4
% 2.53/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.01  --bmc1_ucm_layered_model                none
% 2.53/1.01  --bmc1_ucm_max_lemma_size               10
% 2.53/1.01  
% 2.53/1.01  ------ AIG Options
% 2.53/1.01  
% 2.53/1.01  --aig_mode                              false
% 2.53/1.01  
% 2.53/1.01  ------ Instantiation Options
% 2.53/1.01  
% 2.53/1.01  --instantiation_flag                    true
% 2.53/1.01  --inst_sos_flag                         false
% 2.53/1.01  --inst_sos_phase                        true
% 2.53/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.01  --inst_lit_sel_side                     num_symb
% 2.53/1.01  --inst_solver_per_active                1400
% 2.53/1.01  --inst_solver_calls_frac                1.
% 2.53/1.01  --inst_passive_queue_type               priority_queues
% 2.53/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.01  --inst_passive_queues_freq              [25;2]
% 2.53/1.01  --inst_dismatching                      true
% 2.53/1.01  --inst_eager_unprocessed_to_passive     true
% 2.53/1.01  --inst_prop_sim_given                   true
% 2.53/1.01  --inst_prop_sim_new                     false
% 2.53/1.01  --inst_subs_new                         false
% 2.53/1.01  --inst_eq_res_simp                      false
% 2.53/1.01  --inst_subs_given                       false
% 2.53/1.01  --inst_orphan_elimination               true
% 2.53/1.01  --inst_learning_loop_flag               true
% 2.53/1.01  --inst_learning_start                   3000
% 2.53/1.01  --inst_learning_factor                  2
% 2.53/1.01  --inst_start_prop_sim_after_learn       3
% 2.53/1.01  --inst_sel_renew                        solver
% 2.53/1.01  --inst_lit_activity_flag                true
% 2.53/1.01  --inst_restr_to_given                   false
% 2.53/1.01  --inst_activity_threshold               500
% 2.53/1.01  --inst_out_proof                        true
% 2.53/1.01  
% 2.53/1.01  ------ Resolution Options
% 2.53/1.01  
% 2.53/1.01  --resolution_flag                       true
% 2.53/1.01  --res_lit_sel                           adaptive
% 2.53/1.01  --res_lit_sel_side                      none
% 2.53/1.01  --res_ordering                          kbo
% 2.53/1.01  --res_to_prop_solver                    active
% 2.53/1.01  --res_prop_simpl_new                    false
% 2.53/1.01  --res_prop_simpl_given                  true
% 2.53/1.01  --res_passive_queue_type                priority_queues
% 2.53/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.01  --res_passive_queues_freq               [15;5]
% 2.53/1.01  --res_forward_subs                      full
% 2.53/1.01  --res_backward_subs                     full
% 2.53/1.01  --res_forward_subs_resolution           true
% 2.53/1.01  --res_backward_subs_resolution          true
% 2.53/1.01  --res_orphan_elimination                true
% 2.53/1.01  --res_time_limit                        2.
% 2.53/1.01  --res_out_proof                         true
% 2.53/1.01  
% 2.53/1.01  ------ Superposition Options
% 2.53/1.01  
% 2.53/1.01  --superposition_flag                    true
% 2.53/1.01  --sup_passive_queue_type                priority_queues
% 2.53/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.01  --demod_completeness_check              fast
% 2.53/1.01  --demod_use_ground                      true
% 2.53/1.01  --sup_to_prop_solver                    passive
% 2.53/1.01  --sup_prop_simpl_new                    true
% 2.53/1.01  --sup_prop_simpl_given                  true
% 2.53/1.01  --sup_fun_splitting                     false
% 2.53/1.01  --sup_smt_interval                      50000
% 2.53/1.01  
% 2.53/1.01  ------ Superposition Simplification Setup
% 2.53/1.01  
% 2.53/1.01  --sup_indices_passive                   []
% 2.53/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.01  --sup_full_bw                           [BwDemod]
% 2.53/1.01  --sup_immed_triv                        [TrivRules]
% 2.53/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.01  --sup_immed_bw_main                     []
% 2.53/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.01  
% 2.53/1.01  ------ Combination Options
% 2.53/1.01  
% 2.53/1.01  --comb_res_mult                         3
% 2.53/1.01  --comb_sup_mult                         2
% 2.53/1.01  --comb_inst_mult                        10
% 2.53/1.01  
% 2.53/1.01  ------ Debug Options
% 2.53/1.01  
% 2.53/1.01  --dbg_backtrace                         false
% 2.53/1.01  --dbg_dump_prop_clauses                 false
% 2.53/1.01  --dbg_dump_prop_clauses_file            -
% 2.53/1.01  --dbg_out_stat                          false
% 2.53/1.01  ------ Parsing...
% 2.53/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.53/1.01  
% 2.53/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.53/1.01  
% 2.53/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.53/1.01  
% 2.53/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.53/1.01  ------ Proving...
% 2.53/1.01  ------ Problem Properties 
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  clauses                                 18
% 2.53/1.01  conjectures                             4
% 2.53/1.01  EPR                                     4
% 2.53/1.01  Horn                                    17
% 2.53/1.01  unary                                   6
% 2.53/1.01  binary                                  9
% 2.53/1.01  lits                                    33
% 2.53/1.01  lits eq                                 5
% 2.53/1.01  fd_pure                                 0
% 2.53/1.01  fd_pseudo                               0
% 2.53/1.01  fd_cond                                 1
% 2.53/1.01  fd_pseudo_cond                          0
% 2.53/1.01  AC symbols                              0
% 2.53/1.01  
% 2.53/1.01  ------ Schedule dynamic 5 is on 
% 2.53/1.01  
% 2.53/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  ------ 
% 2.53/1.01  Current options:
% 2.53/1.01  ------ 
% 2.53/1.01  
% 2.53/1.01  ------ Input Options
% 2.53/1.01  
% 2.53/1.01  --out_options                           all
% 2.53/1.01  --tptp_safe_out                         true
% 2.53/1.01  --problem_path                          ""
% 2.53/1.01  --include_path                          ""
% 2.53/1.01  --clausifier                            res/vclausify_rel
% 2.53/1.01  --clausifier_options                    --mode clausify
% 2.53/1.01  --stdin                                 false
% 2.53/1.01  --stats_out                             all
% 2.53/1.01  
% 2.53/1.01  ------ General Options
% 2.53/1.01  
% 2.53/1.01  --fof                                   false
% 2.53/1.01  --time_out_real                         305.
% 2.53/1.01  --time_out_virtual                      -1.
% 2.53/1.01  --symbol_type_check                     false
% 2.53/1.01  --clausify_out                          false
% 2.53/1.01  --sig_cnt_out                           false
% 2.53/1.01  --trig_cnt_out                          false
% 2.53/1.01  --trig_cnt_out_tolerance                1.
% 2.53/1.01  --trig_cnt_out_sk_spl                   false
% 2.53/1.01  --abstr_cl_out                          false
% 2.53/1.01  
% 2.53/1.01  ------ Global Options
% 2.53/1.01  
% 2.53/1.01  --schedule                              default
% 2.53/1.01  --add_important_lit                     false
% 2.53/1.01  --prop_solver_per_cl                    1000
% 2.53/1.01  --min_unsat_core                        false
% 2.53/1.01  --soft_assumptions                      false
% 2.53/1.01  --soft_lemma_size                       3
% 2.53/1.01  --prop_impl_unit_size                   0
% 2.53/1.01  --prop_impl_unit                        []
% 2.53/1.01  --share_sel_clauses                     true
% 2.53/1.01  --reset_solvers                         false
% 2.53/1.01  --bc_imp_inh                            [conj_cone]
% 2.53/1.01  --conj_cone_tolerance                   3.
% 2.53/1.01  --extra_neg_conj                        none
% 2.53/1.01  --large_theory_mode                     true
% 2.53/1.01  --prolific_symb_bound                   200
% 2.53/1.01  --lt_threshold                          2000
% 2.53/1.01  --clause_weak_htbl                      true
% 2.53/1.01  --gc_record_bc_elim                     false
% 2.53/1.01  
% 2.53/1.01  ------ Preprocessing Options
% 2.53/1.01  
% 2.53/1.01  --preprocessing_flag                    true
% 2.53/1.01  --time_out_prep_mult                    0.1
% 2.53/1.01  --splitting_mode                        input
% 2.53/1.01  --splitting_grd                         true
% 2.53/1.01  --splitting_cvd                         false
% 2.53/1.01  --splitting_cvd_svl                     false
% 2.53/1.01  --splitting_nvd                         32
% 2.53/1.01  --sub_typing                            true
% 2.53/1.01  --prep_gs_sim                           true
% 2.53/1.01  --prep_unflatten                        true
% 2.53/1.01  --prep_res_sim                          true
% 2.53/1.01  --prep_upred                            true
% 2.53/1.01  --prep_sem_filter                       exhaustive
% 2.53/1.01  --prep_sem_filter_out                   false
% 2.53/1.01  --pred_elim                             true
% 2.53/1.01  --res_sim_input                         true
% 2.53/1.01  --eq_ax_congr_red                       true
% 2.53/1.01  --pure_diseq_elim                       true
% 2.53/1.01  --brand_transform                       false
% 2.53/1.01  --non_eq_to_eq                          false
% 2.53/1.01  --prep_def_merge                        true
% 2.53/1.01  --prep_def_merge_prop_impl              false
% 2.53/1.01  --prep_def_merge_mbd                    true
% 2.53/1.01  --prep_def_merge_tr_red                 false
% 2.53/1.01  --prep_def_merge_tr_cl                  false
% 2.53/1.01  --smt_preprocessing                     true
% 2.53/1.01  --smt_ac_axioms                         fast
% 2.53/1.01  --preprocessed_out                      false
% 2.53/1.01  --preprocessed_stats                    false
% 2.53/1.01  
% 2.53/1.01  ------ Abstraction refinement Options
% 2.53/1.01  
% 2.53/1.01  --abstr_ref                             []
% 2.53/1.01  --abstr_ref_prep                        false
% 2.53/1.01  --abstr_ref_until_sat                   false
% 2.53/1.01  --abstr_ref_sig_restrict                funpre
% 2.53/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.01  --abstr_ref_under                       []
% 2.53/1.01  
% 2.53/1.01  ------ SAT Options
% 2.53/1.01  
% 2.53/1.01  --sat_mode                              false
% 2.53/1.01  --sat_fm_restart_options                ""
% 2.53/1.01  --sat_gr_def                            false
% 2.53/1.01  --sat_epr_types                         true
% 2.53/1.01  --sat_non_cyclic_types                  false
% 2.53/1.01  --sat_finite_models                     false
% 2.53/1.01  --sat_fm_lemmas                         false
% 2.53/1.01  --sat_fm_prep                           false
% 2.53/1.01  --sat_fm_uc_incr                        true
% 2.53/1.01  --sat_out_model                         small
% 2.53/1.01  --sat_out_clauses                       false
% 2.53/1.01  
% 2.53/1.01  ------ QBF Options
% 2.53/1.01  
% 2.53/1.01  --qbf_mode                              false
% 2.53/1.01  --qbf_elim_univ                         false
% 2.53/1.01  --qbf_dom_inst                          none
% 2.53/1.01  --qbf_dom_pre_inst                      false
% 2.53/1.01  --qbf_sk_in                             false
% 2.53/1.01  --qbf_pred_elim                         true
% 2.53/1.01  --qbf_split                             512
% 2.53/1.01  
% 2.53/1.01  ------ BMC1 Options
% 2.53/1.01  
% 2.53/1.01  --bmc1_incremental                      false
% 2.53/1.01  --bmc1_axioms                           reachable_all
% 2.53/1.01  --bmc1_min_bound                        0
% 2.53/1.01  --bmc1_max_bound                        -1
% 2.53/1.01  --bmc1_max_bound_default                -1
% 2.53/1.01  --bmc1_symbol_reachability              true
% 2.53/1.01  --bmc1_property_lemmas                  false
% 2.53/1.01  --bmc1_k_induction                      false
% 2.53/1.01  --bmc1_non_equiv_states                 false
% 2.53/1.01  --bmc1_deadlock                         false
% 2.53/1.01  --bmc1_ucm                              false
% 2.53/1.01  --bmc1_add_unsat_core                   none
% 2.53/1.01  --bmc1_unsat_core_children              false
% 2.53/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.01  --bmc1_out_stat                         full
% 2.53/1.01  --bmc1_ground_init                      false
% 2.53/1.01  --bmc1_pre_inst_next_state              false
% 2.53/1.01  --bmc1_pre_inst_state                   false
% 2.53/1.01  --bmc1_pre_inst_reach_state             false
% 2.53/1.01  --bmc1_out_unsat_core                   false
% 2.53/1.01  --bmc1_aig_witness_out                  false
% 2.53/1.01  --bmc1_verbose                          false
% 2.53/1.01  --bmc1_dump_clauses_tptp                false
% 2.53/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.01  --bmc1_dump_file                        -
% 2.53/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.01  --bmc1_ucm_extend_mode                  1
% 2.53/1.01  --bmc1_ucm_init_mode                    2
% 2.53/1.01  --bmc1_ucm_cone_mode                    none
% 2.53/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.01  --bmc1_ucm_relax_model                  4
% 2.53/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.01  --bmc1_ucm_layered_model                none
% 2.53/1.01  --bmc1_ucm_max_lemma_size               10
% 2.53/1.01  
% 2.53/1.01  ------ AIG Options
% 2.53/1.01  
% 2.53/1.01  --aig_mode                              false
% 2.53/1.01  
% 2.53/1.01  ------ Instantiation Options
% 2.53/1.01  
% 2.53/1.01  --instantiation_flag                    true
% 2.53/1.01  --inst_sos_flag                         false
% 2.53/1.01  --inst_sos_phase                        true
% 2.53/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.01  --inst_lit_sel_side                     none
% 2.53/1.01  --inst_solver_per_active                1400
% 2.53/1.01  --inst_solver_calls_frac                1.
% 2.53/1.01  --inst_passive_queue_type               priority_queues
% 2.53/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.01  --inst_passive_queues_freq              [25;2]
% 2.53/1.01  --inst_dismatching                      true
% 2.53/1.01  --inst_eager_unprocessed_to_passive     true
% 2.53/1.01  --inst_prop_sim_given                   true
% 2.53/1.01  --inst_prop_sim_new                     false
% 2.53/1.01  --inst_subs_new                         false
% 2.53/1.01  --inst_eq_res_simp                      false
% 2.53/1.01  --inst_subs_given                       false
% 2.53/1.01  --inst_orphan_elimination               true
% 2.53/1.01  --inst_learning_loop_flag               true
% 2.53/1.01  --inst_learning_start                   3000
% 2.53/1.01  --inst_learning_factor                  2
% 2.53/1.01  --inst_start_prop_sim_after_learn       3
% 2.53/1.01  --inst_sel_renew                        solver
% 2.53/1.01  --inst_lit_activity_flag                true
% 2.53/1.01  --inst_restr_to_given                   false
% 2.53/1.01  --inst_activity_threshold               500
% 2.53/1.01  --inst_out_proof                        true
% 2.53/1.01  
% 2.53/1.01  ------ Resolution Options
% 2.53/1.01  
% 2.53/1.01  --resolution_flag                       false
% 2.53/1.01  --res_lit_sel                           adaptive
% 2.53/1.01  --res_lit_sel_side                      none
% 2.53/1.01  --res_ordering                          kbo
% 2.53/1.01  --res_to_prop_solver                    active
% 2.53/1.01  --res_prop_simpl_new                    false
% 2.53/1.01  --res_prop_simpl_given                  true
% 2.53/1.01  --res_passive_queue_type                priority_queues
% 2.53/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.01  --res_passive_queues_freq               [15;5]
% 2.53/1.01  --res_forward_subs                      full
% 2.53/1.01  --res_backward_subs                     full
% 2.53/1.01  --res_forward_subs_resolution           true
% 2.53/1.01  --res_backward_subs_resolution          true
% 2.53/1.01  --res_orphan_elimination                true
% 2.53/1.01  --res_time_limit                        2.
% 2.53/1.01  --res_out_proof                         true
% 2.53/1.01  
% 2.53/1.01  ------ Superposition Options
% 2.53/1.01  
% 2.53/1.01  --superposition_flag                    true
% 2.53/1.01  --sup_passive_queue_type                priority_queues
% 2.53/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.01  --demod_completeness_check              fast
% 2.53/1.01  --demod_use_ground                      true
% 2.53/1.01  --sup_to_prop_solver                    passive
% 2.53/1.01  --sup_prop_simpl_new                    true
% 2.53/1.01  --sup_prop_simpl_given                  true
% 2.53/1.01  --sup_fun_splitting                     false
% 2.53/1.01  --sup_smt_interval                      50000
% 2.53/1.01  
% 2.53/1.01  ------ Superposition Simplification Setup
% 2.53/1.01  
% 2.53/1.01  --sup_indices_passive                   []
% 2.53/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.01  --sup_full_bw                           [BwDemod]
% 2.53/1.01  --sup_immed_triv                        [TrivRules]
% 2.53/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.01  --sup_immed_bw_main                     []
% 2.53/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.01  
% 2.53/1.01  ------ Combination Options
% 2.53/1.01  
% 2.53/1.01  --comb_res_mult                         3
% 2.53/1.01  --comb_sup_mult                         2
% 2.53/1.01  --comb_inst_mult                        10
% 2.53/1.01  
% 2.53/1.01  ------ Debug Options
% 2.53/1.01  
% 2.53/1.01  --dbg_backtrace                         false
% 2.53/1.01  --dbg_dump_prop_clauses                 false
% 2.53/1.01  --dbg_dump_prop_clauses_file            -
% 2.53/1.01  --dbg_out_stat                          false
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  ------ Proving...
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  % SZS status Theorem for theBenchmark.p
% 2.53/1.01  
% 2.53/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.53/1.01  
% 2.53/1.01  fof(f3,axiom,(
% 2.53/1.01    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f20,plain,(
% 2.53/1.01    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 2.53/1.01    inference(ennf_transformation,[],[f3])).
% 2.53/1.01  
% 2.53/1.01  fof(f47,plain,(
% 2.53/1.01    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f20])).
% 2.53/1.01  
% 2.53/1.01  fof(f16,conjecture,(
% 2.53/1.01    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f17,negated_conjecture,(
% 2.53/1.01    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 2.53/1.01    inference(negated_conjecture,[],[f16])).
% 2.53/1.01  
% 2.53/1.01  fof(f32,plain,(
% 2.53/1.01    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.53/1.01    inference(ennf_transformation,[],[f17])).
% 2.53/1.01  
% 2.53/1.01  fof(f33,plain,(
% 2.53/1.01    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.53/1.01    inference(flattening,[],[f32])).
% 2.53/1.01  
% 2.53/1.01  fof(f42,plain,(
% 2.53/1.01    ( ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,sK3)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))) )),
% 2.53/1.01    introduced(choice_axiom,[])).
% 2.53/1.01  
% 2.53/1.01  fof(f41,plain,(
% 2.53/1.01    ( ! [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,sK2,X2)) | ~m1_subset_1(X3,sK2)) & k1_xboole_0 != k1_relset_1(X0,sK2,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) & ~v1_xboole_0(sK2))) )),
% 2.53/1.01    introduced(choice_axiom,[])).
% 2.53/1.01  
% 2.53/1.01  fof(f40,plain,(
% 2.53/1.01    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK1,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK1,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 2.53/1.01    introduced(choice_axiom,[])).
% 2.53/1.01  
% 2.53/1.01  fof(f43,plain,(
% 2.53/1.01    ((! [X3] : (~r2_hidden(X3,k2_relset_1(sK1,sK2,sK3)) | ~m1_subset_1(X3,sK2)) & k1_xboole_0 != k1_relset_1(sK1,sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 2.53/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f42,f41,f40])).
% 2.53/1.01  
% 2.53/1.01  fof(f64,plain,(
% 2.53/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 2.53/1.01    inference(cnf_transformation,[],[f43])).
% 2.53/1.01  
% 2.53/1.01  fof(f15,axiom,(
% 2.53/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f30,plain,(
% 2.53/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.53/1.01    inference(ennf_transformation,[],[f15])).
% 2.53/1.01  
% 2.53/1.01  fof(f31,plain,(
% 2.53/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 2.53/1.01    inference(flattening,[],[f30])).
% 2.53/1.01  
% 2.53/1.01  fof(f61,plain,(
% 2.53/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 2.53/1.01    inference(cnf_transformation,[],[f31])).
% 2.53/1.01  
% 2.53/1.01  fof(f6,axiom,(
% 2.53/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f38,plain,(
% 2.53/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.53/1.01    inference(nnf_transformation,[],[f6])).
% 2.53/1.01  
% 2.53/1.01  fof(f50,plain,(
% 2.53/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.53/1.01    inference(cnf_transformation,[],[f38])).
% 2.53/1.01  
% 2.53/1.01  fof(f14,axiom,(
% 2.53/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f29,plain,(
% 2.53/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.53/1.01    inference(ennf_transformation,[],[f14])).
% 2.53/1.01  
% 2.53/1.01  fof(f60,plain,(
% 2.53/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.53/1.01    inference(cnf_transformation,[],[f29])).
% 2.53/1.01  
% 2.53/1.01  fof(f1,axiom,(
% 2.53/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f34,plain,(
% 2.53/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.53/1.01    inference(nnf_transformation,[],[f1])).
% 2.53/1.01  
% 2.53/1.01  fof(f35,plain,(
% 2.53/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.53/1.01    inference(rectify,[],[f34])).
% 2.53/1.01  
% 2.53/1.01  fof(f36,plain,(
% 2.53/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.53/1.01    introduced(choice_axiom,[])).
% 2.53/1.01  
% 2.53/1.01  fof(f37,plain,(
% 2.53/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.53/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 2.53/1.01  
% 2.53/1.01  fof(f45,plain,(
% 2.53/1.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f37])).
% 2.53/1.01  
% 2.53/1.01  fof(f7,axiom,(
% 2.53/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f21,plain,(
% 2.53/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.53/1.01    inference(ennf_transformation,[],[f7])).
% 2.53/1.01  
% 2.53/1.01  fof(f22,plain,(
% 2.53/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.53/1.01    inference(flattening,[],[f21])).
% 2.53/1.01  
% 2.53/1.01  fof(f52,plain,(
% 2.53/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f22])).
% 2.53/1.01  
% 2.53/1.01  fof(f51,plain,(
% 2.53/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f38])).
% 2.53/1.01  
% 2.53/1.01  fof(f66,plain,(
% 2.53/1.01    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK1,sK2,sK3)) | ~m1_subset_1(X3,sK2)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f43])).
% 2.53/1.01  
% 2.53/1.01  fof(f12,axiom,(
% 2.53/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f18,plain,(
% 2.53/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.53/1.01    inference(pure_predicate_removal,[],[f12])).
% 2.53/1.01  
% 2.53/1.01  fof(f27,plain,(
% 2.53/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.53/1.01    inference(ennf_transformation,[],[f18])).
% 2.53/1.01  
% 2.53/1.01  fof(f58,plain,(
% 2.53/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.53/1.01    inference(cnf_transformation,[],[f27])).
% 2.53/1.01  
% 2.53/1.01  fof(f9,axiom,(
% 2.53/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f24,plain,(
% 2.53/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.53/1.01    inference(ennf_transformation,[],[f9])).
% 2.53/1.01  
% 2.53/1.01  fof(f39,plain,(
% 2.53/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.53/1.01    inference(nnf_transformation,[],[f24])).
% 2.53/1.01  
% 2.53/1.01  fof(f54,plain,(
% 2.53/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f39])).
% 2.53/1.01  
% 2.53/1.01  fof(f11,axiom,(
% 2.53/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f26,plain,(
% 2.53/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.53/1.01    inference(ennf_transformation,[],[f11])).
% 2.53/1.01  
% 2.53/1.01  fof(f57,plain,(
% 2.53/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.53/1.01    inference(cnf_transformation,[],[f26])).
% 2.53/1.01  
% 2.53/1.01  fof(f2,axiom,(
% 2.53/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f19,plain,(
% 2.53/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.53/1.01    inference(ennf_transformation,[],[f2])).
% 2.53/1.01  
% 2.53/1.01  fof(f46,plain,(
% 2.53/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f19])).
% 2.53/1.01  
% 2.53/1.01  fof(f8,axiom,(
% 2.53/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f23,plain,(
% 2.53/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.53/1.01    inference(ennf_transformation,[],[f8])).
% 2.53/1.01  
% 2.53/1.01  fof(f53,plain,(
% 2.53/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f23])).
% 2.53/1.01  
% 2.53/1.01  fof(f5,axiom,(
% 2.53/1.01    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f49,plain,(
% 2.53/1.01    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.53/1.01    inference(cnf_transformation,[],[f5])).
% 2.53/1.01  
% 2.53/1.01  fof(f4,axiom,(
% 2.53/1.01    ! [X0] : k2_subset_1(X0) = X0),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f48,plain,(
% 2.53/1.01    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.53/1.01    inference(cnf_transformation,[],[f4])).
% 2.53/1.01  
% 2.53/1.01  fof(f10,axiom,(
% 2.53/1.01    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f25,plain,(
% 2.53/1.01    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 2.53/1.01    inference(ennf_transformation,[],[f10])).
% 2.53/1.01  
% 2.53/1.01  fof(f56,plain,(
% 2.53/1.01    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.53/1.01    inference(cnf_transformation,[],[f25])).
% 2.53/1.01  
% 2.53/1.01  fof(f13,axiom,(
% 2.53/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.53/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.01  
% 2.53/1.01  fof(f28,plain,(
% 2.53/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.53/1.01    inference(ennf_transformation,[],[f13])).
% 2.53/1.01  
% 2.53/1.01  fof(f59,plain,(
% 2.53/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.53/1.01    inference(cnf_transformation,[],[f28])).
% 2.53/1.01  
% 2.53/1.01  fof(f65,plain,(
% 2.53/1.01    k1_xboole_0 != k1_relset_1(sK1,sK2,sK3)),
% 2.53/1.01    inference(cnf_transformation,[],[f43])).
% 2.53/1.01  
% 2.53/1.01  cnf(c_3,plain,
% 2.53/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 2.53/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1141,plain,
% 2.53/1.01      ( v1_xboole_0(X0) != iProver_top
% 2.53/1.01      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_20,negated_conjecture,
% 2.53/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.53/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1133,plain,
% 2.53/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_17,plain,
% 2.53/1.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.53/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.53/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.53/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1134,plain,
% 2.53/1.01      ( r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.53/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.53/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2253,plain,
% 2.53/1.01      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 2.53/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_1133,c_1134]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_7,plain,
% 2.53/1.01      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.53/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1138,plain,
% 2.53/1.01      ( r1_tarski(X0,X1) = iProver_top
% 2.53/1.01      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2396,plain,
% 2.53/1.01      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 2.53/1.01      | r1_tarski(sK3,k2_zfmisc_1(sK1,X0)) = iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_2253,c_1138]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_16,plain,
% 2.53/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.53/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1135,plain,
% 2.53/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.53/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2039,plain,
% 2.53/1.01      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_1133,c_1135]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_0,plain,
% 2.53/1.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.53/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_8,plain,
% 2.53/1.01      ( m1_subset_1(X0,X1)
% 2.53/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.53/1.01      | ~ r2_hidden(X0,X2) ),
% 2.53/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_336,plain,
% 2.53/1.01      ( m1_subset_1(X0,X1)
% 2.53/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.53/1.01      | v1_xboole_0(X3)
% 2.53/1.01      | X2 != X3
% 2.53/1.01      | sK0(X3) != X0 ),
% 2.53/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_8]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_337,plain,
% 2.53/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.53/1.01      | m1_subset_1(sK0(X0),X1)
% 2.53/1.01      | v1_xboole_0(X0) ),
% 2.53/1.01      inference(unflattening,[status(thm)],[c_336]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_6,plain,
% 2.53/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.53/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_521,plain,
% 2.53/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.53/1.01      inference(prop_impl,[status(thm)],[c_6]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_552,plain,
% 2.53/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(sK0(X0),X1) | v1_xboole_0(X0) ),
% 2.53/1.01      inference(bin_hyper_res,[status(thm)],[c_337,c_521]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1127,plain,
% 2.53/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.53/1.01      | m1_subset_1(sK0(X0),X1) = iProver_top
% 2.53/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_18,negated_conjecture,
% 2.53/1.01      ( ~ m1_subset_1(X0,sK2)
% 2.53/1.01      | ~ r2_hidden(X0,k2_relset_1(sK1,sK2,sK3)) ),
% 2.53/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_364,plain,
% 2.53/1.01      ( ~ m1_subset_1(X0,sK2)
% 2.53/1.01      | v1_xboole_0(X1)
% 2.53/1.01      | k2_relset_1(sK1,sK2,sK3) != X1
% 2.53/1.01      | sK0(X1) != X0 ),
% 2.53/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_18]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_365,plain,
% 2.53/1.01      ( ~ m1_subset_1(sK0(k2_relset_1(sK1,sK2,sK3)),sK2)
% 2.53/1.01      | v1_xboole_0(k2_relset_1(sK1,sK2,sK3)) ),
% 2.53/1.01      inference(unflattening,[status(thm)],[c_364]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1128,plain,
% 2.53/1.01      ( m1_subset_1(sK0(k2_relset_1(sK1,sK2,sK3)),sK2) != iProver_top
% 2.53/1.01      | v1_xboole_0(k2_relset_1(sK1,sK2,sK3)) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1480,plain,
% 2.53/1.01      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2) != iProver_top
% 2.53/1.01      | v1_xboole_0(k2_relset_1(sK1,sK2,sK3)) = iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_1127,c_1128]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_25,plain,
% 2.53/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_14,plain,
% 2.53/1.01      ( v5_relat_1(X0,X1)
% 2.53/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.53/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_11,plain,
% 2.53/1.01      ( ~ v5_relat_1(X0,X1)
% 2.53/1.01      | r1_tarski(k2_relat_1(X0),X1)
% 2.53/1.01      | ~ v1_relat_1(X0) ),
% 2.53/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_314,plain,
% 2.53/1.01      ( r1_tarski(k2_relat_1(X0),X1)
% 2.53/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.53/1.01      | ~ v1_relat_1(X0) ),
% 2.53/1.01      inference(resolution,[status(thm)],[c_14,c_11]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_13,plain,
% 2.53/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.01      | v1_relat_1(X0) ),
% 2.53/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_324,plain,
% 2.53/1.01      ( r1_tarski(k2_relat_1(X0),X1)
% 2.53/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.53/1.01      inference(forward_subsumption_resolution,
% 2.53/1.01                [status(thm)],
% 2.53/1.01                [c_314,c_13]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1265,plain,
% 2.53/1.01      ( r1_tarski(k2_relat_1(sK3),sK2)
% 2.53/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_324]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1266,plain,
% 2.53/1.01      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 2.53/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_1265]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1298,plain,
% 2.53/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 2.53/1.01      | k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_730,plain,
% 2.53/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 2.53/1.01      theory(equality) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1342,plain,
% 2.53/1.01      ( ~ r1_tarski(X0,sK2)
% 2.53/1.01      | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
% 2.53/1.01      | k2_relset_1(sK1,sK2,sK3) != X0 ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_730]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1427,plain,
% 2.53/1.01      ( r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2)
% 2.53/1.01      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 2.53/1.01      | k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3) ),
% 2.53/1.01      inference(instantiation,[status(thm)],[c_1342]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1428,plain,
% 2.53/1.01      ( k2_relset_1(sK1,sK2,sK3) != k2_relat_1(sK3)
% 2.53/1.01      | r1_tarski(k2_relset_1(sK1,sK2,sK3),sK2) = iProver_top
% 2.53/1.01      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_1427]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1731,plain,
% 2.53/1.01      ( v1_xboole_0(k2_relset_1(sK1,sK2,sK3)) = iProver_top ),
% 2.53/1.01      inference(global_propositional_subsumption,
% 2.53/1.01                [status(thm)],
% 2.53/1.01                [c_1480,c_20,c_25,c_1266,c_1298,c_1428]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2,plain,
% 2.53/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.53/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1142,plain,
% 2.53/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1736,plain,
% 2.53/1.01      ( k2_relset_1(sK1,sK2,sK3) = k1_xboole_0 ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_1731,c_1142]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2051,plain,
% 2.53/1.01      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 2.53/1.01      inference(light_normalisation,[status(thm)],[c_2039,c_1736]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2516,plain,
% 2.53/1.01      ( r1_tarski(sK3,k2_zfmisc_1(sK1,X0)) = iProver_top
% 2.53/1.01      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 2.53/1.01      inference(light_normalisation,[status(thm)],[c_2396,c_2051]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_9,plain,
% 2.53/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.53/1.01      | ~ r2_hidden(X2,X0)
% 2.53/1.01      | ~ v1_xboole_0(X1) ),
% 2.53/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_167,plain,
% 2.53/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.53/1.01      inference(prop_impl,[status(thm)],[c_6]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_207,plain,
% 2.53/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 2.53/1.01      inference(bin_hyper_res,[status(thm)],[c_9,c_167]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_351,plain,
% 2.53/1.01      ( ~ r1_tarski(X0,X1)
% 2.53/1.01      | ~ v1_xboole_0(X1)
% 2.53/1.01      | v1_xboole_0(X2)
% 2.53/1.01      | X0 != X2
% 2.53/1.01      | sK0(X2) != X3 ),
% 2.53/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_207]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_352,plain,
% 2.53/1.01      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 2.53/1.01      inference(unflattening,[status(thm)],[c_351]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1129,plain,
% 2.53/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.53/1.01      | v1_xboole_0(X1) != iProver_top
% 2.53/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_352]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2520,plain,
% 2.53/1.01      ( r1_tarski(k1_xboole_0,X0) != iProver_top
% 2.53/1.01      | v1_xboole_0(k2_zfmisc_1(sK1,X0)) != iProver_top
% 2.53/1.01      | v1_xboole_0(sK3) = iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_2516,c_1129]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_3656,plain,
% 2.53/1.01      ( r1_tarski(k1_xboole_0,X0) != iProver_top
% 2.53/1.01      | v1_xboole_0(X0) != iProver_top
% 2.53/1.01      | v1_xboole_0(sK3) = iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_1141,c_2520]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1738,plain,
% 2.53/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.53/1.01      inference(demodulation,[status(thm)],[c_1736,c_1731]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1560,plain,
% 2.53/1.01      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 2.53/1.01      | v1_xboole_0(X1) != iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_1141,c_1142]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_3010,plain,
% 2.53/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_1738,c_1560]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2418,plain,
% 2.53/1.01      ( r1_tarski(k1_xboole_0,X0) != iProver_top
% 2.53/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top ),
% 2.53/1.01      inference(demodulation,[status(thm)],[c_2051,c_2253]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_3328,plain,
% 2.53/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.53/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_3010,c_2418]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_5,plain,
% 2.53/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.53/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1140,plain,
% 2.53/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_4,plain,
% 2.53/1.01      ( k2_subset_1(X0) = X0 ),
% 2.53/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1151,plain,
% 2.53/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.53/1.01      inference(light_normalisation,[status(thm)],[c_1140,c_4]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1567,plain,
% 2.53/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_1151,c_1138]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_3494,plain,
% 2.53/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.53/1.01      inference(forward_subsumption_resolution,
% 2.53/1.01                [status(thm)],
% 2.53/1.01                [c_3328,c_1567]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_3496,plain,
% 2.53/1.01      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_3494,c_1138]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_3737,plain,
% 2.53/1.01      ( v1_xboole_0(sK3) = iProver_top
% 2.53/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_3496,c_1129]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_4999,plain,
% 2.53/1.01      ( v1_xboole_0(sK3) = iProver_top ),
% 2.53/1.01      inference(global_propositional_subsumption,
% 2.53/1.01                [status(thm)],
% 2.53/1.01                [c_3656,c_1738,c_3737]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_12,plain,
% 2.53/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0)) ),
% 2.53/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1137,plain,
% 2.53/1.01      ( v1_xboole_0(X0) != iProver_top
% 2.53/1.01      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1485,plain,
% 2.53/1.01      ( k1_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_1137,c_1142]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_5006,plain,
% 2.53/1.01      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_4999,c_1485]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_15,plain,
% 2.53/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.53/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.53/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_1136,plain,
% 2.53/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.53/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.53/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2224,plain,
% 2.53/1.01      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.53/1.01      inference(superposition,[status(thm)],[c_1133,c_1136]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_19,negated_conjecture,
% 2.53/1.01      ( k1_xboole_0 != k1_relset_1(sK1,sK2,sK3) ),
% 2.53/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(c_2338,plain,
% 2.53/1.01      ( k1_relat_1(sK3) != k1_xboole_0 ),
% 2.53/1.01      inference(demodulation,[status(thm)],[c_2224,c_19]) ).
% 2.53/1.01  
% 2.53/1.01  cnf(contradiction,plain,
% 2.53/1.01      ( $false ),
% 2.53/1.01      inference(minisat,[status(thm)],[c_5006,c_2338]) ).
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.53/1.01  
% 2.53/1.01  ------                               Statistics
% 2.53/1.01  
% 2.53/1.01  ------ General
% 2.53/1.01  
% 2.53/1.01  abstr_ref_over_cycles:                  0
% 2.53/1.01  abstr_ref_under_cycles:                 0
% 2.53/1.01  gc_basic_clause_elim:                   0
% 2.53/1.01  forced_gc_time:                         0
% 2.53/1.01  parsing_time:                           0.01
% 2.53/1.01  unif_index_cands_time:                  0.
% 2.53/1.01  unif_index_add_time:                    0.
% 2.53/1.01  orderings_time:                         0.
% 2.53/1.01  out_proof_time:                         0.008
% 2.53/1.01  total_time:                             0.165
% 2.53/1.01  num_of_symbols:                         49
% 2.53/1.01  num_of_terms:                           5177
% 2.53/1.01  
% 2.53/1.01  ------ Preprocessing
% 2.53/1.01  
% 2.53/1.01  num_of_splits:                          0
% 2.53/1.01  num_of_split_atoms:                     0
% 2.53/1.01  num_of_reused_defs:                     0
% 2.53/1.01  num_eq_ax_congr_red:                    16
% 2.53/1.01  num_of_sem_filtered_clauses:            1
% 2.53/1.01  num_of_subtypes:                        0
% 2.53/1.01  monotx_restored_types:                  0
% 2.53/1.01  sat_num_of_epr_types:                   0
% 2.53/1.01  sat_num_of_non_cyclic_types:            0
% 2.53/1.01  sat_guarded_non_collapsed_types:        0
% 2.53/1.01  num_pure_diseq_elim:                    0
% 2.53/1.01  simp_replaced_by:                       0
% 2.53/1.01  res_preprocessed:                       98
% 2.53/1.01  prep_upred:                             0
% 2.53/1.01  prep_unflattend:                        22
% 2.53/1.01  smt_new_axioms:                         0
% 2.53/1.01  pred_elim_cands:                        3
% 2.53/1.01  pred_elim:                              3
% 2.53/1.01  pred_elim_cl:                           5
% 2.53/1.01  pred_elim_cycles:                       6
% 2.53/1.01  merged_defs:                            8
% 2.53/1.01  merged_defs_ncl:                        0
% 2.53/1.01  bin_hyper_res:                          10
% 2.53/1.01  prep_cycles:                            4
% 2.53/1.01  pred_elim_time:                         0.005
% 2.53/1.01  splitting_time:                         0.
% 2.53/1.01  sem_filter_time:                        0.
% 2.53/1.01  monotx_time:                            0.
% 2.53/1.01  subtype_inf_time:                       0.
% 2.53/1.01  
% 2.53/1.01  ------ Problem properties
% 2.53/1.01  
% 2.53/1.01  clauses:                                18
% 2.53/1.01  conjectures:                            4
% 2.53/1.01  epr:                                    4
% 2.53/1.01  horn:                                   17
% 2.53/1.01  ground:                                 5
% 2.53/1.01  unary:                                  6
% 2.53/1.01  binary:                                 9
% 2.53/1.01  lits:                                   33
% 2.53/1.01  lits_eq:                                5
% 2.53/1.01  fd_pure:                                0
% 2.53/1.01  fd_pseudo:                              0
% 2.53/1.01  fd_cond:                                1
% 2.53/1.01  fd_pseudo_cond:                         0
% 2.53/1.01  ac_symbols:                             0
% 2.53/1.01  
% 2.53/1.01  ------ Propositional Solver
% 2.53/1.01  
% 2.53/1.01  prop_solver_calls:                      29
% 2.53/1.01  prop_fast_solver_calls:                 574
% 2.53/1.01  smt_solver_calls:                       0
% 2.53/1.01  smt_fast_solver_calls:                  0
% 2.53/1.01  prop_num_of_clauses:                    1979
% 2.53/1.01  prop_preprocess_simplified:             5734
% 2.53/1.01  prop_fo_subsumed:                       3
% 2.53/1.01  prop_solver_time:                       0.
% 2.53/1.01  smt_solver_time:                        0.
% 2.53/1.01  smt_fast_solver_time:                   0.
% 2.53/1.01  prop_fast_solver_time:                  0.
% 2.53/1.01  prop_unsat_core_time:                   0.
% 2.53/1.01  
% 2.53/1.01  ------ QBF
% 2.53/1.01  
% 2.53/1.01  qbf_q_res:                              0
% 2.53/1.01  qbf_num_tautologies:                    0
% 2.53/1.01  qbf_prep_cycles:                        0
% 2.53/1.01  
% 2.53/1.01  ------ BMC1
% 2.53/1.01  
% 2.53/1.01  bmc1_current_bound:                     -1
% 2.53/1.01  bmc1_last_solved_bound:                 -1
% 2.53/1.01  bmc1_unsat_core_size:                   -1
% 2.53/1.01  bmc1_unsat_core_parents_size:           -1
% 2.53/1.01  bmc1_merge_next_fun:                    0
% 2.53/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.53/1.01  
% 2.53/1.01  ------ Instantiation
% 2.53/1.01  
% 2.53/1.01  inst_num_of_clauses:                    640
% 2.53/1.01  inst_num_in_passive:                    205
% 2.53/1.01  inst_num_in_active:                     306
% 2.53/1.01  inst_num_in_unprocessed:                129
% 2.53/1.01  inst_num_of_loops:                      320
% 2.53/1.01  inst_num_of_learning_restarts:          0
% 2.53/1.01  inst_num_moves_active_passive:          11
% 2.53/1.01  inst_lit_activity:                      0
% 2.53/1.01  inst_lit_activity_moves:                0
% 2.53/1.01  inst_num_tautologies:                   0
% 2.53/1.01  inst_num_prop_implied:                  0
% 2.53/1.01  inst_num_existing_simplified:           0
% 2.53/1.01  inst_num_eq_res_simplified:             0
% 2.53/1.01  inst_num_child_elim:                    0
% 2.53/1.01  inst_num_of_dismatching_blockings:      196
% 2.53/1.01  inst_num_of_non_proper_insts:           613
% 2.53/1.01  inst_num_of_duplicates:                 0
% 2.53/1.01  inst_inst_num_from_inst_to_res:         0
% 2.53/1.01  inst_dismatching_checking_time:         0.
% 2.53/1.01  
% 2.53/1.01  ------ Resolution
% 2.53/1.01  
% 2.53/1.01  res_num_of_clauses:                     0
% 2.53/1.01  res_num_in_passive:                     0
% 2.53/1.01  res_num_in_active:                      0
% 2.53/1.01  res_num_of_loops:                       102
% 2.53/1.01  res_forward_subset_subsumed:            59
% 2.53/1.01  res_backward_subset_subsumed:           0
% 2.53/1.01  res_forward_subsumed:                   0
% 2.53/1.01  res_backward_subsumed:                  0
% 2.53/1.01  res_forward_subsumption_resolution:     1
% 2.53/1.01  res_backward_subsumption_resolution:    0
% 2.53/1.01  res_clause_to_clause_subsumption:       366
% 2.53/1.01  res_orphan_elimination:                 0
% 2.53/1.01  res_tautology_del:                      99
% 2.53/1.01  res_num_eq_res_simplified:              0
% 2.53/1.01  res_num_sel_changes:                    0
% 2.53/1.01  res_moves_from_active_to_pass:          0
% 2.53/1.01  
% 2.53/1.01  ------ Superposition
% 2.53/1.01  
% 2.53/1.01  sup_time_total:                         0.
% 2.53/1.01  sup_time_generating:                    0.
% 2.53/1.01  sup_time_sim_full:                      0.
% 2.53/1.01  sup_time_sim_immed:                     0.
% 2.53/1.01  
% 2.53/1.01  sup_num_of_clauses:                     93
% 2.53/1.01  sup_num_in_active:                      59
% 2.53/1.01  sup_num_in_passive:                     34
% 2.53/1.01  sup_num_of_loops:                       63
% 2.53/1.01  sup_fw_superposition:                   75
% 2.53/1.01  sup_bw_superposition:                   47
% 2.53/1.01  sup_immediate_simplified:               27
% 2.53/1.01  sup_given_eliminated:                   1
% 2.53/1.01  comparisons_done:                       0
% 2.53/1.01  comparisons_avoided:                    0
% 2.53/1.01  
% 2.53/1.01  ------ Simplifications
% 2.53/1.01  
% 2.53/1.01  
% 2.53/1.01  sim_fw_subset_subsumed:                 3
% 2.53/1.01  sim_bw_subset_subsumed:                 2
% 2.53/1.01  sim_fw_subsumed:                        6
% 2.53/1.01  sim_bw_subsumed:                        2
% 2.53/1.01  sim_fw_subsumption_res:                 1
% 2.53/1.01  sim_bw_subsumption_res:                 0
% 2.53/1.01  sim_tautology_del:                      5
% 2.53/1.01  sim_eq_tautology_del:                   10
% 2.53/1.01  sim_eq_res_simp:                        0
% 2.53/1.01  sim_fw_demodulated:                     1
% 2.53/1.01  sim_bw_demodulated:                     10
% 2.53/1.01  sim_light_normalised:                   30
% 2.53/1.01  sim_joinable_taut:                      0
% 2.53/1.01  sim_joinable_simp:                      0
% 2.53/1.01  sim_ac_normalised:                      0
% 2.53/1.01  sim_smt_subsumption:                    0
% 2.53/1.01  
%------------------------------------------------------------------------------
