%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:56:40 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  153 (1099 expanded)
%              Number of clauses        :   90 ( 444 expanded)
%              Number of leaves         :   21 ( 200 expanded)
%              Depth                    :   20
%              Number of atoms          :  381 (3225 expanded)
%              Number of equality atoms :  187 ( 905 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f38])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f18,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
            & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k1_relset_1(X0,X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k1_relset_1(X0,X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k1_relset_1(X0,X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(sK2,sK3,sK4))
          | ~ m1_subset_1(X3,sK3) )
      & k1_xboole_0 != k1_relset_1(sK2,sK3,sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK2,sK3,sK4))
        | ~ m1_subset_1(X3,sK3) )
    & k1_xboole_0 != k1_relset_1(sK2,sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f43])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK2,sK3,sK4))
      | ~ m1_subset_1(X3,sK3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f36])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    k1_xboole_0 != k1_relset_1(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1431,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1418,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_328,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_8])).

cnf(c_1415,plain,
    ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_1676,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1418,c_1415])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1430,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1428,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2905,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X2,X1) = iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1430,c_1428])).

cnf(c_3429,plain,
    ( m1_subset_1(X0,sK3) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1676,c_2905])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1429,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1643,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1418,c_1429])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_186,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_229,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_186])).

cnf(c_1417,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_2141,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1643,c_1417])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1427,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2244,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2141,c_1427])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1420,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2387,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1418,c_1420])).

cnf(c_20,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | ~ r2_hidden(X0,k2_relset_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1419,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | r2_hidden(X0,k2_relset_1(sK2,sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2505,plain,
    ( m1_subset_1(X0,sK3) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2387,c_1419])).

cnf(c_2876,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK3)
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2877,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2876])).

cnf(c_3291,plain,
    ( m1_subset_1(X0,sK3)
    | ~ m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3))
    | ~ r2_hidden(X0,k2_relat_1(sK4)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3292,plain,
    ( m1_subset_1(X0,sK3) = iProver_top
    | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) != iProver_top
    | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3291])).

cnf(c_3440,plain,
    ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3429,c_1676,c_2244,c_2505,c_2877,c_3292])).

cnf(c_3447,plain,
    ( k2_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1431,c_3440])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1426,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3543,plain,
    ( sK4 = k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3447,c_1426])).

cnf(c_1700,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1706,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | k1_xboole_0 = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1700])).

cnf(c_913,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1711,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_914,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1873,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_2534,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1873])).

cnf(c_2535,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2534])).

cnf(c_3630,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3543,c_1706,c_1711,c_2244,c_2535,c_3447])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_310,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_17,c_10])).

cnf(c_1416,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_2311,plain,
    ( k7_relat_1(sK4,sK2) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1418,c_1416])).

cnf(c_2629,plain,
    ( k7_relat_1(sK4,sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2311,c_2244])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1424,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2246,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = k3_xboole_0(k1_relat_1(sK4),X0) ),
    inference(superposition,[status(thm)],[c_2244,c_1424])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1433,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2925,plain,
    ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK4,X1))) != iProver_top
    | r1_xboole_0(k1_relat_1(sK4),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2246,c_1433])).

cnf(c_3091,plain,
    ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
    | r1_xboole_0(k1_relat_1(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2629,c_2925])).

cnf(c_3637,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | r1_xboole_0(k1_relat_1(k1_xboole_0),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3630,c_3091])).

cnf(c_15,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1422,plain,
    ( k7_relat_1(X0,X1) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2632,plain,
    ( sK4 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK4),sK2) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2629,c_1422])).

cnf(c_2695,plain,
    ( r1_xboole_0(k1_relat_1(sK4),sK2) = iProver_top
    | sK4 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2632,c_2244])).

cnf(c_2696,plain,
    ( sK4 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK4),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2695])).

cnf(c_3641,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(k1_xboole_0),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3630,c_2696])).

cnf(c_3660,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3641])).

cnf(c_3671,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3637,c_3660])).

cnf(c_4768,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1431,c_3671])).

cnf(c_1617,plain,
    ( k1_relset_1(sK2,sK3,sK4) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relset_1(sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_2644,plain,
    ( k1_relset_1(sK2,sK3,sK4) != k1_relat_1(X0)
    | k1_xboole_0 = k1_relset_1(sK2,sK3,sK4)
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1617])).

cnf(c_2646,plain,
    ( k1_relset_1(sK2,sK3,sK4) != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(sK2,sK3,sK4)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2644])).

cnf(c_923,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_2232,plain,
    ( X0 != sK4
    | k1_relat_1(X0) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_923])).

cnf(c_2234,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(sK4)
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2232])).

cnf(c_1692,plain,
    ( X0 != X1
    | k1_relset_1(sK2,sK3,sK4) != X1
    | k1_relset_1(sK2,sK3,sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_1848,plain,
    ( X0 != k1_relat_1(sK4)
    | k1_relset_1(sK2,sK3,sK4) = X0
    | k1_relset_1(sK2,sK3,sK4) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1692])).

cnf(c_2231,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(X0)
    | k1_relset_1(sK2,sK3,sK4) != k1_relat_1(sK4)
    | k1_relat_1(X0) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1848])).

cnf(c_2233,plain,
    ( k1_relset_1(sK2,sK3,sK4) != k1_relat_1(sK4)
    | k1_relset_1(sK2,sK3,sK4) = k1_relat_1(k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2231])).

cnf(c_2054,plain,
    ( X0 != X1
    | X0 = k1_relat_1(X2)
    | k1_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_914])).

cnf(c_2055,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2054])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1619,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_938,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_913])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != k1_relset_1(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4768,c_3447,c_2646,c_2244,c_2234,c_2233,c_2055,c_1706,c_1619,c_938,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:16:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.08/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/0.97  
% 2.08/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.08/0.97  
% 2.08/0.97  ------  iProver source info
% 2.08/0.97  
% 2.08/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.08/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.08/0.97  git: non_committed_changes: false
% 2.08/0.97  git: last_make_outside_of_git: false
% 2.08/0.97  
% 2.08/0.97  ------ 
% 2.08/0.97  
% 2.08/0.97  ------ Input Options
% 2.08/0.97  
% 2.08/0.97  --out_options                           all
% 2.08/0.97  --tptp_safe_out                         true
% 2.08/0.97  --problem_path                          ""
% 2.08/0.97  --include_path                          ""
% 2.08/0.97  --clausifier                            res/vclausify_rel
% 2.08/0.97  --clausifier_options                    --mode clausify
% 2.08/0.97  --stdin                                 false
% 2.08/0.97  --stats_out                             all
% 2.08/0.97  
% 2.08/0.97  ------ General Options
% 2.08/0.97  
% 2.08/0.97  --fof                                   false
% 2.08/0.97  --time_out_real                         305.
% 2.08/0.97  --time_out_virtual                      -1.
% 2.08/0.97  --symbol_type_check                     false
% 2.08/0.97  --clausify_out                          false
% 2.08/0.97  --sig_cnt_out                           false
% 2.08/0.97  --trig_cnt_out                          false
% 2.08/0.97  --trig_cnt_out_tolerance                1.
% 2.08/0.97  --trig_cnt_out_sk_spl                   false
% 2.08/0.97  --abstr_cl_out                          false
% 2.08/0.97  
% 2.08/0.97  ------ Global Options
% 2.08/0.97  
% 2.08/0.97  --schedule                              default
% 2.08/0.97  --add_important_lit                     false
% 2.08/0.97  --prop_solver_per_cl                    1000
% 2.08/0.97  --min_unsat_core                        false
% 2.08/0.97  --soft_assumptions                      false
% 2.08/0.97  --soft_lemma_size                       3
% 2.08/0.97  --prop_impl_unit_size                   0
% 2.08/0.97  --prop_impl_unit                        []
% 2.08/0.97  --share_sel_clauses                     true
% 2.08/0.97  --reset_solvers                         false
% 2.08/0.97  --bc_imp_inh                            [conj_cone]
% 2.08/0.97  --conj_cone_tolerance                   3.
% 2.08/0.97  --extra_neg_conj                        none
% 2.08/0.97  --large_theory_mode                     true
% 2.08/0.97  --prolific_symb_bound                   200
% 2.08/0.97  --lt_threshold                          2000
% 2.08/0.97  --clause_weak_htbl                      true
% 2.08/0.97  --gc_record_bc_elim                     false
% 2.08/0.97  
% 2.08/0.97  ------ Preprocessing Options
% 2.08/0.97  
% 2.08/0.97  --preprocessing_flag                    true
% 2.08/0.97  --time_out_prep_mult                    0.1
% 2.08/0.97  --splitting_mode                        input
% 2.08/0.97  --splitting_grd                         true
% 2.08/0.97  --splitting_cvd                         false
% 2.08/0.97  --splitting_cvd_svl                     false
% 2.08/0.97  --splitting_nvd                         32
% 2.08/0.97  --sub_typing                            true
% 2.08/0.97  --prep_gs_sim                           true
% 2.08/0.97  --prep_unflatten                        true
% 2.08/0.97  --prep_res_sim                          true
% 2.08/0.97  --prep_upred                            true
% 2.08/0.97  --prep_sem_filter                       exhaustive
% 2.08/0.97  --prep_sem_filter_out                   false
% 2.08/0.97  --pred_elim                             true
% 2.08/0.97  --res_sim_input                         true
% 2.08/0.97  --eq_ax_congr_red                       true
% 2.08/0.97  --pure_diseq_elim                       true
% 2.08/0.97  --brand_transform                       false
% 2.08/0.97  --non_eq_to_eq                          false
% 2.08/0.97  --prep_def_merge                        true
% 2.08/0.97  --prep_def_merge_prop_impl              false
% 2.08/0.97  --prep_def_merge_mbd                    true
% 2.08/0.97  --prep_def_merge_tr_red                 false
% 2.08/0.97  --prep_def_merge_tr_cl                  false
% 2.08/0.97  --smt_preprocessing                     true
% 2.08/0.97  --smt_ac_axioms                         fast
% 2.08/0.97  --preprocessed_out                      false
% 2.08/0.97  --preprocessed_stats                    false
% 2.08/0.97  
% 2.08/0.97  ------ Abstraction refinement Options
% 2.08/0.97  
% 2.08/0.97  --abstr_ref                             []
% 2.08/0.97  --abstr_ref_prep                        false
% 2.08/0.97  --abstr_ref_until_sat                   false
% 2.08/0.97  --abstr_ref_sig_restrict                funpre
% 2.08/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/0.97  --abstr_ref_under                       []
% 2.08/0.97  
% 2.08/0.97  ------ SAT Options
% 2.08/0.97  
% 2.08/0.97  --sat_mode                              false
% 2.08/0.97  --sat_fm_restart_options                ""
% 2.08/0.97  --sat_gr_def                            false
% 2.08/0.97  --sat_epr_types                         true
% 2.08/0.97  --sat_non_cyclic_types                  false
% 2.08/0.97  --sat_finite_models                     false
% 2.08/0.97  --sat_fm_lemmas                         false
% 2.08/0.97  --sat_fm_prep                           false
% 2.08/0.97  --sat_fm_uc_incr                        true
% 2.08/0.97  --sat_out_model                         small
% 2.08/0.97  --sat_out_clauses                       false
% 2.08/0.97  
% 2.08/0.97  ------ QBF Options
% 2.08/0.97  
% 2.08/0.97  --qbf_mode                              false
% 2.08/0.97  --qbf_elim_univ                         false
% 2.08/0.97  --qbf_dom_inst                          none
% 2.08/0.97  --qbf_dom_pre_inst                      false
% 2.08/0.97  --qbf_sk_in                             false
% 2.08/0.97  --qbf_pred_elim                         true
% 2.08/0.97  --qbf_split                             512
% 2.08/0.97  
% 2.08/0.97  ------ BMC1 Options
% 2.08/0.97  
% 2.08/0.97  --bmc1_incremental                      false
% 2.08/0.97  --bmc1_axioms                           reachable_all
% 2.08/0.97  --bmc1_min_bound                        0
% 2.08/0.97  --bmc1_max_bound                        -1
% 2.08/0.97  --bmc1_max_bound_default                -1
% 2.08/0.97  --bmc1_symbol_reachability              true
% 2.08/0.97  --bmc1_property_lemmas                  false
% 2.08/0.97  --bmc1_k_induction                      false
% 2.08/0.97  --bmc1_non_equiv_states                 false
% 2.08/0.97  --bmc1_deadlock                         false
% 2.08/0.97  --bmc1_ucm                              false
% 2.08/0.97  --bmc1_add_unsat_core                   none
% 2.08/0.97  --bmc1_unsat_core_children              false
% 2.08/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/0.97  --bmc1_out_stat                         full
% 2.08/0.97  --bmc1_ground_init                      false
% 2.08/0.97  --bmc1_pre_inst_next_state              false
% 2.08/0.97  --bmc1_pre_inst_state                   false
% 2.08/0.97  --bmc1_pre_inst_reach_state             false
% 2.08/0.97  --bmc1_out_unsat_core                   false
% 2.08/0.97  --bmc1_aig_witness_out                  false
% 2.08/0.97  --bmc1_verbose                          false
% 2.08/0.97  --bmc1_dump_clauses_tptp                false
% 2.08/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.08/0.97  --bmc1_dump_file                        -
% 2.08/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.08/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.08/0.97  --bmc1_ucm_extend_mode                  1
% 2.08/0.97  --bmc1_ucm_init_mode                    2
% 2.08/0.97  --bmc1_ucm_cone_mode                    none
% 2.08/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.08/0.97  --bmc1_ucm_relax_model                  4
% 2.08/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.08/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/0.97  --bmc1_ucm_layered_model                none
% 2.08/0.97  --bmc1_ucm_max_lemma_size               10
% 2.08/0.97  
% 2.08/0.97  ------ AIG Options
% 2.08/0.97  
% 2.08/0.97  --aig_mode                              false
% 2.08/0.97  
% 2.08/0.97  ------ Instantiation Options
% 2.08/0.97  
% 2.08/0.97  --instantiation_flag                    true
% 2.08/0.97  --inst_sos_flag                         false
% 2.08/0.97  --inst_sos_phase                        true
% 2.08/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/0.97  --inst_lit_sel_side                     num_symb
% 2.08/0.97  --inst_solver_per_active                1400
% 2.08/0.97  --inst_solver_calls_frac                1.
% 2.08/0.97  --inst_passive_queue_type               priority_queues
% 2.08/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/0.97  --inst_passive_queues_freq              [25;2]
% 2.08/0.97  --inst_dismatching                      true
% 2.08/0.97  --inst_eager_unprocessed_to_passive     true
% 2.08/0.97  --inst_prop_sim_given                   true
% 2.08/0.97  --inst_prop_sim_new                     false
% 2.08/0.97  --inst_subs_new                         false
% 2.08/0.97  --inst_eq_res_simp                      false
% 2.08/0.97  --inst_subs_given                       false
% 2.08/0.97  --inst_orphan_elimination               true
% 2.08/0.97  --inst_learning_loop_flag               true
% 2.08/0.97  --inst_learning_start                   3000
% 2.08/0.97  --inst_learning_factor                  2
% 2.08/0.97  --inst_start_prop_sim_after_learn       3
% 2.08/0.97  --inst_sel_renew                        solver
% 2.08/0.97  --inst_lit_activity_flag                true
% 2.08/0.97  --inst_restr_to_given                   false
% 2.08/0.97  --inst_activity_threshold               500
% 2.08/0.97  --inst_out_proof                        true
% 2.08/0.97  
% 2.08/0.97  ------ Resolution Options
% 2.08/0.97  
% 2.08/0.97  --resolution_flag                       true
% 2.08/0.97  --res_lit_sel                           adaptive
% 2.08/0.97  --res_lit_sel_side                      none
% 2.08/0.97  --res_ordering                          kbo
% 2.08/0.97  --res_to_prop_solver                    active
% 2.08/0.97  --res_prop_simpl_new                    false
% 2.08/0.97  --res_prop_simpl_given                  true
% 2.08/0.97  --res_passive_queue_type                priority_queues
% 2.08/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/0.97  --res_passive_queues_freq               [15;5]
% 2.08/0.97  --res_forward_subs                      full
% 2.08/0.97  --res_backward_subs                     full
% 2.08/0.97  --res_forward_subs_resolution           true
% 2.08/0.97  --res_backward_subs_resolution          true
% 2.08/0.97  --res_orphan_elimination                true
% 2.08/0.97  --res_time_limit                        2.
% 2.08/0.97  --res_out_proof                         true
% 2.08/0.97  
% 2.08/0.97  ------ Superposition Options
% 2.08/0.97  
% 2.08/0.97  --superposition_flag                    true
% 2.08/0.97  --sup_passive_queue_type                priority_queues
% 2.08/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.08/0.97  --demod_completeness_check              fast
% 2.08/0.97  --demod_use_ground                      true
% 2.08/0.97  --sup_to_prop_solver                    passive
% 2.08/0.97  --sup_prop_simpl_new                    true
% 2.08/0.97  --sup_prop_simpl_given                  true
% 2.08/0.97  --sup_fun_splitting                     false
% 2.08/0.97  --sup_smt_interval                      50000
% 2.08/0.97  
% 2.08/0.97  ------ Superposition Simplification Setup
% 2.08/0.97  
% 2.08/0.97  --sup_indices_passive                   []
% 2.08/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.97  --sup_full_bw                           [BwDemod]
% 2.08/0.97  --sup_immed_triv                        [TrivRules]
% 2.08/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.97  --sup_immed_bw_main                     []
% 2.08/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.97  
% 2.08/0.97  ------ Combination Options
% 2.08/0.97  
% 2.08/0.97  --comb_res_mult                         3
% 2.08/0.97  --comb_sup_mult                         2
% 2.08/0.97  --comb_inst_mult                        10
% 2.08/0.97  
% 2.08/0.97  ------ Debug Options
% 2.08/0.97  
% 2.08/0.97  --dbg_backtrace                         false
% 2.08/0.97  --dbg_dump_prop_clauses                 false
% 2.08/0.97  --dbg_dump_prop_clauses_file            -
% 2.08/0.97  --dbg_out_stat                          false
% 2.08/0.97  ------ Parsing...
% 2.08/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.08/0.97  
% 2.08/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.08/0.97  
% 2.08/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.08/0.97  
% 2.08/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.08/0.97  ------ Proving...
% 2.08/0.97  ------ Problem Properties 
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  clauses                                 20
% 2.08/0.97  conjectures                             3
% 2.08/0.97  EPR                                     1
% 2.08/0.97  Horn                                    18
% 2.08/0.97  unary                                   3
% 2.08/0.97  binary                                  9
% 2.08/0.97  lits                                    45
% 2.08/0.97  lits eq                                 12
% 2.08/0.97  fd_pure                                 0
% 2.08/0.97  fd_pseudo                               0
% 2.08/0.97  fd_cond                                 3
% 2.08/0.97  fd_pseudo_cond                          0
% 2.08/0.97  AC symbols                              0
% 2.08/0.97  
% 2.08/0.97  ------ Schedule dynamic 5 is on 
% 2.08/0.97  
% 2.08/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.08/0.97  
% 2.08/0.97  
% 2.08/0.97  ------ 
% 2.08/0.97  Current options:
% 2.08/0.97  ------ 
% 2.08/0.97  
% 2.08/0.97  ------ Input Options
% 2.08/0.97  
% 2.08/0.97  --out_options                           all
% 2.08/0.97  --tptp_safe_out                         true
% 2.08/0.97  --problem_path                          ""
% 2.08/0.97  --include_path                          ""
% 2.08/0.97  --clausifier                            res/vclausify_rel
% 2.08/0.97  --clausifier_options                    --mode clausify
% 2.08/0.97  --stdin                                 false
% 2.08/0.97  --stats_out                             all
% 2.08/0.97  
% 2.08/0.97  ------ General Options
% 2.08/0.97  
% 2.08/0.97  --fof                                   false
% 2.08/0.97  --time_out_real                         305.
% 2.08/0.97  --time_out_virtual                      -1.
% 2.08/0.97  --symbol_type_check                     false
% 2.08/0.97  --clausify_out                          false
% 2.08/0.97  --sig_cnt_out                           false
% 2.08/0.97  --trig_cnt_out                          false
% 2.08/0.97  --trig_cnt_out_tolerance                1.
% 2.08/0.97  --trig_cnt_out_sk_spl                   false
% 2.08/0.97  --abstr_cl_out                          false
% 2.08/0.97  
% 2.08/0.97  ------ Global Options
% 2.08/0.97  
% 2.08/0.97  --schedule                              default
% 2.08/0.97  --add_important_lit                     false
% 2.08/0.97  --prop_solver_per_cl                    1000
% 2.08/0.97  --min_unsat_core                        false
% 2.08/0.97  --soft_assumptions                      false
% 2.08/0.97  --soft_lemma_size                       3
% 2.08/0.97  --prop_impl_unit_size                   0
% 2.08/0.97  --prop_impl_unit                        []
% 2.08/0.97  --share_sel_clauses                     true
% 2.08/0.97  --reset_solvers                         false
% 2.08/0.97  --bc_imp_inh                            [conj_cone]
% 2.08/0.97  --conj_cone_tolerance                   3.
% 2.08/0.97  --extra_neg_conj                        none
% 2.08/0.97  --large_theory_mode                     true
% 2.08/0.97  --prolific_symb_bound                   200
% 2.08/0.97  --lt_threshold                          2000
% 2.08/0.97  --clause_weak_htbl                      true
% 2.08/0.97  --gc_record_bc_elim                     false
% 2.08/0.97  
% 2.08/0.97  ------ Preprocessing Options
% 2.08/0.97  
% 2.08/0.97  --preprocessing_flag                    true
% 2.08/0.97  --time_out_prep_mult                    0.1
% 2.08/0.97  --splitting_mode                        input
% 2.08/0.97  --splitting_grd                         true
% 2.08/0.97  --splitting_cvd                         false
% 2.08/0.97  --splitting_cvd_svl                     false
% 2.08/0.97  --splitting_nvd                         32
% 2.08/0.97  --sub_typing                            true
% 2.08/0.97  --prep_gs_sim                           true
% 2.08/0.97  --prep_unflatten                        true
% 2.08/0.97  --prep_res_sim                          true
% 2.08/0.97  --prep_upred                            true
% 2.08/0.97  --prep_sem_filter                       exhaustive
% 2.08/0.97  --prep_sem_filter_out                   false
% 2.08/0.97  --pred_elim                             true
% 2.08/0.97  --res_sim_input                         true
% 2.08/0.97  --eq_ax_congr_red                       true
% 2.08/0.97  --pure_diseq_elim                       true
% 2.08/0.97  --brand_transform                       false
% 2.08/0.97  --non_eq_to_eq                          false
% 2.08/0.97  --prep_def_merge                        true
% 2.08/0.97  --prep_def_merge_prop_impl              false
% 2.08/0.97  --prep_def_merge_mbd                    true
% 2.08/0.97  --prep_def_merge_tr_red                 false
% 2.08/0.97  --prep_def_merge_tr_cl                  false
% 2.08/0.97  --smt_preprocessing                     true
% 2.08/0.97  --smt_ac_axioms                         fast
% 2.08/0.97  --preprocessed_out                      false
% 2.08/0.97  --preprocessed_stats                    false
% 2.08/0.97  
% 2.08/0.97  ------ Abstraction refinement Options
% 2.08/0.97  
% 2.08/0.97  --abstr_ref                             []
% 2.08/0.97  --abstr_ref_prep                        false
% 2.08/0.97  --abstr_ref_until_sat                   false
% 2.08/0.97  --abstr_ref_sig_restrict                funpre
% 2.08/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.08/0.97  --abstr_ref_under                       []
% 2.08/0.97  
% 2.08/0.97  ------ SAT Options
% 2.08/0.97  
% 2.08/0.97  --sat_mode                              false
% 2.08/0.97  --sat_fm_restart_options                ""
% 2.08/0.97  --sat_gr_def                            false
% 2.08/0.97  --sat_epr_types                         true
% 2.08/0.97  --sat_non_cyclic_types                  false
% 2.08/0.97  --sat_finite_models                     false
% 2.08/0.97  --sat_fm_lemmas                         false
% 2.08/0.97  --sat_fm_prep                           false
% 2.08/0.97  --sat_fm_uc_incr                        true
% 2.08/0.97  --sat_out_model                         small
% 2.08/0.97  --sat_out_clauses                       false
% 2.08/0.97  
% 2.08/0.97  ------ QBF Options
% 2.08/0.97  
% 2.08/0.97  --qbf_mode                              false
% 2.08/0.97  --qbf_elim_univ                         false
% 2.08/0.97  --qbf_dom_inst                          none
% 2.08/0.97  --qbf_dom_pre_inst                      false
% 2.08/0.97  --qbf_sk_in                             false
% 2.08/0.97  --qbf_pred_elim                         true
% 2.08/0.97  --qbf_split                             512
% 2.08/0.97  
% 2.08/0.97  ------ BMC1 Options
% 2.08/0.97  
% 2.08/0.97  --bmc1_incremental                      false
% 2.08/0.97  --bmc1_axioms                           reachable_all
% 2.08/0.97  --bmc1_min_bound                        0
% 2.08/0.97  --bmc1_max_bound                        -1
% 2.08/0.97  --bmc1_max_bound_default                -1
% 2.08/0.97  --bmc1_symbol_reachability              true
% 2.08/0.97  --bmc1_property_lemmas                  false
% 2.08/0.97  --bmc1_k_induction                      false
% 2.08/0.97  --bmc1_non_equiv_states                 false
% 2.08/0.97  --bmc1_deadlock                         false
% 2.08/0.97  --bmc1_ucm                              false
% 2.08/0.97  --bmc1_add_unsat_core                   none
% 2.08/0.97  --bmc1_unsat_core_children              false
% 2.08/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.08/0.97  --bmc1_out_stat                         full
% 2.08/0.97  --bmc1_ground_init                      false
% 2.08/0.97  --bmc1_pre_inst_next_state              false
% 2.08/0.97  --bmc1_pre_inst_state                   false
% 2.08/0.97  --bmc1_pre_inst_reach_state             false
% 2.08/0.97  --bmc1_out_unsat_core                   false
% 2.08/0.97  --bmc1_aig_witness_out                  false
% 2.08/0.97  --bmc1_verbose                          false
% 2.08/0.97  --bmc1_dump_clauses_tptp                false
% 2.08/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.08/0.97  --bmc1_dump_file                        -
% 2.08/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.08/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.08/0.97  --bmc1_ucm_extend_mode                  1
% 2.08/0.97  --bmc1_ucm_init_mode                    2
% 2.08/0.97  --bmc1_ucm_cone_mode                    none
% 2.08/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.08/0.97  --bmc1_ucm_relax_model                  4
% 2.08/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.08/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.08/0.97  --bmc1_ucm_layered_model                none
% 2.08/0.97  --bmc1_ucm_max_lemma_size               10
% 2.08/0.97  
% 2.08/0.97  ------ AIG Options
% 2.08/0.97  
% 2.08/0.97  --aig_mode                              false
% 2.08/0.97  
% 2.08/0.97  ------ Instantiation Options
% 2.08/0.97  
% 2.08/0.97  --instantiation_flag                    true
% 2.08/0.97  --inst_sos_flag                         false
% 2.08/0.97  --inst_sos_phase                        true
% 2.08/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.08/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.08/0.97  --inst_lit_sel_side                     none
% 2.08/0.97  --inst_solver_per_active                1400
% 2.08/0.97  --inst_solver_calls_frac                1.
% 2.08/0.97  --inst_passive_queue_type               priority_queues
% 2.08/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.08/0.97  --inst_passive_queues_freq              [25;2]
% 2.08/0.97  --inst_dismatching                      true
% 2.08/0.97  --inst_eager_unprocessed_to_passive     true
% 2.08/0.97  --inst_prop_sim_given                   true
% 2.08/0.97  --inst_prop_sim_new                     false
% 2.08/0.97  --inst_subs_new                         false
% 2.08/0.97  --inst_eq_res_simp                      false
% 2.08/0.97  --inst_subs_given                       false
% 2.08/0.97  --inst_orphan_elimination               true
% 2.08/0.97  --inst_learning_loop_flag               true
% 2.08/0.97  --inst_learning_start                   3000
% 2.08/0.97  --inst_learning_factor                  2
% 2.08/0.97  --inst_start_prop_sim_after_learn       3
% 2.08/0.97  --inst_sel_renew                        solver
% 2.08/0.97  --inst_lit_activity_flag                true
% 2.08/0.97  --inst_restr_to_given                   false
% 2.08/0.97  --inst_activity_threshold               500
% 2.08/0.97  --inst_out_proof                        true
% 2.08/0.97  
% 2.08/0.97  ------ Resolution Options
% 2.08/0.97  
% 2.08/0.97  --resolution_flag                       false
% 2.08/0.97  --res_lit_sel                           adaptive
% 2.08/0.97  --res_lit_sel_side                      none
% 2.08/0.97  --res_ordering                          kbo
% 2.08/0.97  --res_to_prop_solver                    active
% 2.08/0.97  --res_prop_simpl_new                    false
% 2.08/0.97  --res_prop_simpl_given                  true
% 2.08/0.97  --res_passive_queue_type                priority_queues
% 2.08/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.08/0.97  --res_passive_queues_freq               [15;5]
% 2.08/0.97  --res_forward_subs                      full
% 2.08/0.97  --res_backward_subs                     full
% 2.08/0.97  --res_forward_subs_resolution           true
% 2.08/0.97  --res_backward_subs_resolution          true
% 2.08/0.97  --res_orphan_elimination                true
% 2.08/0.97  --res_time_limit                        2.
% 2.08/0.97  --res_out_proof                         true
% 2.08/0.97  
% 2.08/0.97  ------ Superposition Options
% 2.08/0.97  
% 2.08/0.97  --superposition_flag                    true
% 2.08/0.97  --sup_passive_queue_type                priority_queues
% 2.08/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.08/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.08/0.97  --demod_completeness_check              fast
% 2.08/0.98  --demod_use_ground                      true
% 2.08/0.98  --sup_to_prop_solver                    passive
% 2.08/0.98  --sup_prop_simpl_new                    true
% 2.08/0.98  --sup_prop_simpl_given                  true
% 2.08/0.98  --sup_fun_splitting                     false
% 2.08/0.98  --sup_smt_interval                      50000
% 2.08/0.98  
% 2.08/0.98  ------ Superposition Simplification Setup
% 2.08/0.98  
% 2.08/0.98  --sup_indices_passive                   []
% 2.08/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.08/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.08/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.98  --sup_full_bw                           [BwDemod]
% 2.08/0.98  --sup_immed_triv                        [TrivRules]
% 2.08/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.08/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.98  --sup_immed_bw_main                     []
% 2.08/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.08/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.08/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.08/0.98  
% 2.08/0.98  ------ Combination Options
% 2.08/0.98  
% 2.08/0.98  --comb_res_mult                         3
% 2.08/0.98  --comb_sup_mult                         2
% 2.08/0.98  --comb_inst_mult                        10
% 2.08/0.98  
% 2.08/0.98  ------ Debug Options
% 2.08/0.98  
% 2.08/0.98  --dbg_backtrace                         false
% 2.08/0.98  --dbg_dump_prop_clauses                 false
% 2.08/0.98  --dbg_dump_prop_clauses_file            -
% 2.08/0.98  --dbg_out_stat                          false
% 2.08/0.98  
% 2.08/0.98  
% 2.08/0.98  
% 2.08/0.98  
% 2.08/0.98  ------ Proving...
% 2.08/0.98  
% 2.08/0.98  
% 2.08/0.98  % SZS status Theorem for theBenchmark.p
% 2.08/0.98  
% 2.08/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.08/0.98  
% 2.08/0.98  fof(f2,axiom,(
% 2.08/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.98  
% 2.08/0.98  fof(f20,plain,(
% 2.08/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.08/0.98    inference(ennf_transformation,[],[f2])).
% 2.08/0.98  
% 2.08/0.98  fof(f38,plain,(
% 2.08/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 2.08/0.98    introduced(choice_axiom,[])).
% 2.08/0.98  
% 2.08/0.98  fof(f39,plain,(
% 2.08/0.98    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 2.08/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f38])).
% 2.08/0.98  
% 2.08/0.98  fof(f47,plain,(
% 2.08/0.98    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.08/0.98    inference(cnf_transformation,[],[f39])).
% 2.08/0.98  
% 2.08/0.98  fof(f15,conjecture,(
% 2.08/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 2.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.98  
% 2.08/0.98  fof(f16,negated_conjecture,(
% 2.08/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 2.08/0.98    inference(negated_conjecture,[],[f15])).
% 2.08/0.98  
% 2.08/0.98  fof(f18,plain,(
% 2.08/0.98    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))),
% 2.08/0.98    inference(pure_predicate_removal,[],[f16])).
% 2.08/0.98  
% 2.08/0.98  fof(f34,plain,(
% 2.08/0.98    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.08/0.98    inference(ennf_transformation,[],[f18])).
% 2.08/0.98  
% 2.08/0.98  fof(f35,plain,(
% 2.08/0.98    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.08/0.98    inference(flattening,[],[f34])).
% 2.08/0.98  
% 2.08/0.98  fof(f43,plain,(
% 2.08/0.98    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(sK2,sK3,sK4)) | ~m1_subset_1(X3,sK3)) & k1_xboole_0 != k1_relset_1(sK2,sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))))),
% 2.08/0.98    introduced(choice_axiom,[])).
% 2.08/0.98  
% 2.08/0.98  fof(f44,plain,(
% 2.08/0.98    ! [X3] : (~r2_hidden(X3,k2_relset_1(sK2,sK3,sK4)) | ~m1_subset_1(X3,sK3)) & k1_xboole_0 != k1_relset_1(sK2,sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.08/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f35,f43])).
% 2.08/0.98  
% 2.08/0.98  fof(f65,plain,(
% 2.08/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.08/0.98    inference(cnf_transformation,[],[f44])).
% 2.08/0.98  
% 2.08/0.98  fof(f12,axiom,(
% 2.08/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.98  
% 2.08/0.98  fof(f31,plain,(
% 2.08/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.08/0.98    inference(ennf_transformation,[],[f12])).
% 2.08/0.98  
% 2.08/0.98  fof(f62,plain,(
% 2.08/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.08/0.98    inference(cnf_transformation,[],[f31])).
% 2.08/0.98  
% 2.08/0.98  fof(f6,axiom,(
% 2.08/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.98  
% 2.08/0.98  fof(f24,plain,(
% 2.08/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.08/0.98    inference(ennf_transformation,[],[f6])).
% 2.08/0.98  
% 2.08/0.98  fof(f41,plain,(
% 2.08/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.08/0.98    inference(nnf_transformation,[],[f24])).
% 2.08/0.98  
% 2.08/0.98  fof(f52,plain,(
% 2.08/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.08/0.98    inference(cnf_transformation,[],[f41])).
% 2.08/0.98  
% 2.08/0.98  fof(f3,axiom,(
% 2.08/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.98  
% 2.08/0.98  fof(f40,plain,(
% 2.08/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.08/0.98    inference(nnf_transformation,[],[f3])).
% 2.08/0.98  
% 2.08/0.98  fof(f49,plain,(
% 2.08/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.08/0.98    inference(cnf_transformation,[],[f40])).
% 2.08/0.98  
% 2.08/0.98  fof(f4,axiom,(
% 2.08/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.98  
% 2.08/0.98  fof(f21,plain,(
% 2.08/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.08/0.98    inference(ennf_transformation,[],[f4])).
% 2.08/0.98  
% 2.08/0.98  fof(f22,plain,(
% 2.08/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.08/0.98    inference(flattening,[],[f21])).
% 2.08/0.98  
% 2.08/0.98  fof(f50,plain,(
% 2.08/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.08/0.98    inference(cnf_transformation,[],[f22])).
% 2.08/0.98  
% 2.08/0.98  fof(f48,plain,(
% 2.08/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.08/0.98    inference(cnf_transformation,[],[f40])).
% 2.08/0.98  
% 2.08/0.98  fof(f5,axiom,(
% 2.08/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.98  
% 2.08/0.98  fof(f23,plain,(
% 2.08/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.08/0.98    inference(ennf_transformation,[],[f5])).
% 2.08/0.98  
% 2.08/0.98  fof(f51,plain,(
% 2.08/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.08/0.98    inference(cnf_transformation,[],[f23])).
% 2.08/0.98  
% 2.08/0.98  fof(f7,axiom,(
% 2.08/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.98  
% 2.08/0.98  fof(f54,plain,(
% 2.08/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.08/0.98    inference(cnf_transformation,[],[f7])).
% 2.08/0.98  
% 2.08/0.98  fof(f14,axiom,(
% 2.08/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.98  
% 2.08/0.98  fof(f33,plain,(
% 2.08/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.08/0.98    inference(ennf_transformation,[],[f14])).
% 2.08/0.98  
% 2.08/0.98  fof(f64,plain,(
% 2.08/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.08/0.98    inference(cnf_transformation,[],[f33])).
% 2.08/0.98  
% 2.08/0.98  fof(f67,plain,(
% 2.08/0.98    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK2,sK3,sK4)) | ~m1_subset_1(X3,sK3)) )),
% 2.08/0.98    inference(cnf_transformation,[],[f44])).
% 2.08/0.98  
% 2.08/0.98  fof(f9,axiom,(
% 2.08/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.98  
% 2.08/0.98  fof(f27,plain,(
% 2.08/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.08/0.98    inference(ennf_transformation,[],[f9])).
% 2.08/0.98  
% 2.08/0.98  fof(f28,plain,(
% 2.08/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.08/0.98    inference(flattening,[],[f27])).
% 2.08/0.98  
% 2.08/0.98  fof(f57,plain,(
% 2.08/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.08/0.98    inference(cnf_transformation,[],[f28])).
% 2.08/0.98  
% 2.08/0.98  fof(f61,plain,(
% 2.08/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.08/0.98    inference(cnf_transformation,[],[f31])).
% 2.08/0.98  
% 2.08/0.98  fof(f8,axiom,(
% 2.08/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.98  
% 2.08/0.98  fof(f25,plain,(
% 2.08/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.08/0.98    inference(ennf_transformation,[],[f8])).
% 2.08/0.98  
% 2.08/0.98  fof(f26,plain,(
% 2.08/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.08/0.98    inference(flattening,[],[f25])).
% 2.08/0.98  
% 2.08/0.98  fof(f55,plain,(
% 2.08/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.08/0.98    inference(cnf_transformation,[],[f26])).
% 2.08/0.98  
% 2.08/0.98  fof(f10,axiom,(
% 2.08/0.98    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 2.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.98  
% 2.08/0.98  fof(f29,plain,(
% 2.08/0.98    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.08/0.98    inference(ennf_transformation,[],[f10])).
% 2.08/0.98  
% 2.08/0.98  fof(f58,plain,(
% 2.08/0.98    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.08/0.98    inference(cnf_transformation,[],[f29])).
% 2.08/0.98  
% 2.08/0.98  fof(f1,axiom,(
% 2.08/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.98  
% 2.08/0.98  fof(f17,plain,(
% 2.08/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.08/0.98    inference(rectify,[],[f1])).
% 2.08/0.98  
% 2.08/0.98  fof(f19,plain,(
% 2.08/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.08/0.98    inference(ennf_transformation,[],[f17])).
% 2.08/0.98  
% 2.08/0.98  fof(f36,plain,(
% 2.08/0.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 2.08/0.98    introduced(choice_axiom,[])).
% 2.08/0.98  
% 2.08/0.98  fof(f37,plain,(
% 2.08/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.08/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f36])).
% 2.08/0.98  
% 2.08/0.98  fof(f46,plain,(
% 2.08/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.08/0.98    inference(cnf_transformation,[],[f37])).
% 2.08/0.98  
% 2.08/0.98  fof(f11,axiom,(
% 2.08/0.98    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 2.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.98  
% 2.08/0.98  fof(f30,plain,(
% 2.08/0.98    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.08/0.98    inference(ennf_transformation,[],[f11])).
% 2.08/0.98  
% 2.08/0.98  fof(f42,plain,(
% 2.08/0.98    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.08/0.98    inference(nnf_transformation,[],[f30])).
% 2.08/0.98  
% 2.08/0.98  fof(f59,plain,(
% 2.08/0.98    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.08/0.98    inference(cnf_transformation,[],[f42])).
% 2.08/0.98  
% 2.08/0.98  fof(f13,axiom,(
% 2.08/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.08/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.08/0.98  
% 2.08/0.98  fof(f32,plain,(
% 2.08/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.08/0.98    inference(ennf_transformation,[],[f13])).
% 2.08/0.98  
% 2.08/0.98  fof(f63,plain,(
% 2.08/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.08/0.98    inference(cnf_transformation,[],[f32])).
% 2.08/0.98  
% 2.08/0.98  fof(f66,plain,(
% 2.08/0.98    k1_xboole_0 != k1_relset_1(sK2,sK3,sK4)),
% 2.08/0.98    inference(cnf_transformation,[],[f44])).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2,plain,
% 2.08/0.98      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.08/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1431,plain,
% 2.08/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_22,negated_conjecture,
% 2.08/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.08/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1418,plain,
% 2.08/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_16,plain,
% 2.08/0.98      ( v5_relat_1(X0,X1)
% 2.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.08/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_8,plain,
% 2.08/0.98      ( ~ v5_relat_1(X0,X1)
% 2.08/0.98      | r1_tarski(k2_relat_1(X0),X1)
% 2.08/0.98      | ~ v1_relat_1(X0) ),
% 2.08/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_328,plain,
% 2.08/0.98      ( r1_tarski(k2_relat_1(X0),X1)
% 2.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.08/0.98      | ~ v1_relat_1(X0) ),
% 2.08/0.98      inference(resolution,[status(thm)],[c_16,c_8]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1415,plain,
% 2.08/0.98      ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 2.08/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 2.08/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1676,plain,
% 2.08/0.98      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top
% 2.08/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.08/0.98      inference(superposition,[status(thm)],[c_1418,c_1415]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_3,plain,
% 2.08/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.08/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1430,plain,
% 2.08/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.08/0.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_5,plain,
% 2.08/0.98      ( m1_subset_1(X0,X1)
% 2.08/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.08/0.98      | ~ r2_hidden(X0,X2) ),
% 2.08/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1428,plain,
% 2.08/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 2.08/0.98      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.08/0.98      | r2_hidden(X0,X2) != iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2905,plain,
% 2.08/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.08/0.98      | m1_subset_1(X2,X1) = iProver_top
% 2.08/0.98      | r2_hidden(X2,X0) != iProver_top ),
% 2.08/0.98      inference(superposition,[status(thm)],[c_1430,c_1428]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_3429,plain,
% 2.08/0.98      ( m1_subset_1(X0,sK3) = iProver_top
% 2.08/0.98      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top
% 2.08/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.08/0.98      inference(superposition,[status(thm)],[c_1676,c_2905]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_4,plain,
% 2.08/0.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.08/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1429,plain,
% 2.08/0.98      ( r1_tarski(X0,X1) = iProver_top
% 2.08/0.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1643,plain,
% 2.08/0.98      ( r1_tarski(sK4,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 2.08/0.98      inference(superposition,[status(thm)],[c_1418,c_1429]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_6,plain,
% 2.08/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.08/0.98      | ~ v1_relat_1(X1)
% 2.08/0.98      | v1_relat_1(X0) ),
% 2.08/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_186,plain,
% 2.08/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.08/0.98      inference(prop_impl,[status(thm)],[c_3]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_229,plain,
% 2.08/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.08/0.98      inference(bin_hyper_res,[status(thm)],[c_6,c_186]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1417,plain,
% 2.08/0.98      ( r1_tarski(X0,X1) != iProver_top
% 2.08/0.98      | v1_relat_1(X1) != iProver_top
% 2.08/0.98      | v1_relat_1(X0) = iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2141,plain,
% 2.08/0.98      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 2.08/0.98      | v1_relat_1(sK4) = iProver_top ),
% 2.08/0.98      inference(superposition,[status(thm)],[c_1643,c_1417]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_9,plain,
% 2.08/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.08/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1427,plain,
% 2.08/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2244,plain,
% 2.08/0.98      ( v1_relat_1(sK4) = iProver_top ),
% 2.08/0.98      inference(forward_subsumption_resolution,
% 2.08/0.98                [status(thm)],
% 2.08/0.98                [c_2141,c_1427]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_19,plain,
% 2.08/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.08/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.08/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1420,plain,
% 2.08/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.08/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2387,plain,
% 2.08/0.98      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 2.08/0.98      inference(superposition,[status(thm)],[c_1418,c_1420]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_20,negated_conjecture,
% 2.08/0.98      ( ~ m1_subset_1(X0,sK3)
% 2.08/0.98      | ~ r2_hidden(X0,k2_relset_1(sK2,sK3,sK4)) ),
% 2.08/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1419,plain,
% 2.08/0.98      ( m1_subset_1(X0,sK3) != iProver_top
% 2.08/0.98      | r2_hidden(X0,k2_relset_1(sK2,sK3,sK4)) != iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2505,plain,
% 2.08/0.98      ( m1_subset_1(X0,sK3) != iProver_top
% 2.08/0.98      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 2.08/0.98      inference(demodulation,[status(thm)],[c_2387,c_1419]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2876,plain,
% 2.08/0.98      ( ~ r1_tarski(k2_relat_1(sK4),sK3)
% 2.08/0.98      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2877,plain,
% 2.08/0.98      ( r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 2.08/0.98      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_2876]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_3291,plain,
% 2.08/0.98      ( m1_subset_1(X0,sK3)
% 2.08/0.98      | ~ m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3))
% 2.08/0.98      | ~ r2_hidden(X0,k2_relat_1(sK4)) ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_3292,plain,
% 2.08/0.98      ( m1_subset_1(X0,sK3) = iProver_top
% 2.08/0.98      | m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) != iProver_top
% 2.08/0.98      | r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_3291]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_3440,plain,
% 2.08/0.98      ( r2_hidden(X0,k2_relat_1(sK4)) != iProver_top ),
% 2.08/0.98      inference(global_propositional_subsumption,
% 2.08/0.98                [status(thm)],
% 2.08/0.98                [c_3429,c_1676,c_2244,c_2505,c_2877,c_3292]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_3447,plain,
% 2.08/0.98      ( k2_relat_1(sK4) = k1_xboole_0 ),
% 2.08/0.98      inference(superposition,[status(thm)],[c_1431,c_3440]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_11,plain,
% 2.08/0.98      ( ~ v1_relat_1(X0)
% 2.08/0.98      | k2_relat_1(X0) != k1_xboole_0
% 2.08/0.98      | k1_xboole_0 = X0 ),
% 2.08/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1426,plain,
% 2.08/0.98      ( k2_relat_1(X0) != k1_xboole_0
% 2.08/0.98      | k1_xboole_0 = X0
% 2.08/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_3543,plain,
% 2.08/0.98      ( sK4 = k1_xboole_0 | v1_relat_1(sK4) != iProver_top ),
% 2.08/0.98      inference(superposition,[status(thm)],[c_3447,c_1426]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1700,plain,
% 2.08/0.98      ( ~ v1_relat_1(sK4)
% 2.08/0.98      | k2_relat_1(sK4) != k1_xboole_0
% 2.08/0.98      | k1_xboole_0 = sK4 ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1706,plain,
% 2.08/0.98      ( k2_relat_1(sK4) != k1_xboole_0
% 2.08/0.98      | k1_xboole_0 = sK4
% 2.08/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_1700]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_913,plain,( X0 = X0 ),theory(equality) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1711,plain,
% 2.08/0.98      ( sK4 = sK4 ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_913]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_914,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1873,plain,
% 2.08/0.98      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_914]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2534,plain,
% 2.08/0.98      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_1873]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2535,plain,
% 2.08/0.98      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_2534]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_3630,plain,
% 2.08/0.98      ( sK4 = k1_xboole_0 ),
% 2.08/0.98      inference(global_propositional_subsumption,
% 2.08/0.98                [status(thm)],
% 2.08/0.98                [c_3543,c_1706,c_1711,c_2244,c_2535,c_3447]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_17,plain,
% 2.08/0.98      ( v4_relat_1(X0,X1)
% 2.08/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.08/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_10,plain,
% 2.08/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.08/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_310,plain,
% 2.08/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.08/0.98      | ~ v1_relat_1(X0)
% 2.08/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.08/0.98      inference(resolution,[status(thm)],[c_17,c_10]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1416,plain,
% 2.08/0.98      ( k7_relat_1(X0,X1) = X0
% 2.08/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.08/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2311,plain,
% 2.08/0.98      ( k7_relat_1(sK4,sK2) = sK4 | v1_relat_1(sK4) != iProver_top ),
% 2.08/0.98      inference(superposition,[status(thm)],[c_1418,c_1416]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2629,plain,
% 2.08/0.98      ( k7_relat_1(sK4,sK2) = sK4 ),
% 2.08/0.98      inference(global_propositional_subsumption,
% 2.08/0.98                [status(thm)],
% 2.08/0.98                [c_2311,c_2244]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_13,plain,
% 2.08/0.98      ( ~ v1_relat_1(X0)
% 2.08/0.98      | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
% 2.08/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1424,plain,
% 2.08/0.98      ( k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)
% 2.08/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2246,plain,
% 2.08/0.98      ( k1_relat_1(k7_relat_1(sK4,X0)) = k3_xboole_0(k1_relat_1(sK4),X0) ),
% 2.08/0.98      inference(superposition,[status(thm)],[c_2244,c_1424]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_0,plain,
% 2.08/0.98      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 2.08/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1433,plain,
% 2.08/0.98      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 2.08/0.98      | r1_xboole_0(X1,X2) != iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2925,plain,
% 2.08/0.98      ( r2_hidden(X0,k1_relat_1(k7_relat_1(sK4,X1))) != iProver_top
% 2.08/0.98      | r1_xboole_0(k1_relat_1(sK4),X1) != iProver_top ),
% 2.08/0.98      inference(superposition,[status(thm)],[c_2246,c_1433]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_3091,plain,
% 2.08/0.98      ( r2_hidden(X0,k1_relat_1(sK4)) != iProver_top
% 2.08/0.98      | r1_xboole_0(k1_relat_1(sK4),sK2) != iProver_top ),
% 2.08/0.98      inference(superposition,[status(thm)],[c_2629,c_2925]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_3637,plain,
% 2.08/0.98      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 2.08/0.98      | r1_xboole_0(k1_relat_1(k1_xboole_0),sK2) != iProver_top ),
% 2.08/0.98      inference(demodulation,[status(thm)],[c_3630,c_3091]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_15,plain,
% 2.08/0.98      ( r1_xboole_0(k1_relat_1(X0),X1)
% 2.08/0.98      | ~ v1_relat_1(X0)
% 2.08/0.98      | k7_relat_1(X0,X1) != k1_xboole_0 ),
% 2.08/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1422,plain,
% 2.08/0.98      ( k7_relat_1(X0,X1) != k1_xboole_0
% 2.08/0.98      | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
% 2.08/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.08/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2632,plain,
% 2.08/0.98      ( sK4 != k1_xboole_0
% 2.08/0.98      | r1_xboole_0(k1_relat_1(sK4),sK2) = iProver_top
% 2.08/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.08/0.98      inference(superposition,[status(thm)],[c_2629,c_1422]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2695,plain,
% 2.08/0.98      ( r1_xboole_0(k1_relat_1(sK4),sK2) = iProver_top
% 2.08/0.98      | sK4 != k1_xboole_0 ),
% 2.08/0.98      inference(global_propositional_subsumption,
% 2.08/0.98                [status(thm)],
% 2.08/0.98                [c_2632,c_2244]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2696,plain,
% 2.08/0.98      ( sK4 != k1_xboole_0
% 2.08/0.98      | r1_xboole_0(k1_relat_1(sK4),sK2) = iProver_top ),
% 2.08/0.98      inference(renaming,[status(thm)],[c_2695]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_3641,plain,
% 2.08/0.98      ( k1_xboole_0 != k1_xboole_0
% 2.08/0.98      | r1_xboole_0(k1_relat_1(k1_xboole_0),sK2) = iProver_top ),
% 2.08/0.98      inference(demodulation,[status(thm)],[c_3630,c_2696]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_3660,plain,
% 2.08/0.98      ( r1_xboole_0(k1_relat_1(k1_xboole_0),sK2) = iProver_top ),
% 2.08/0.98      inference(equality_resolution_simp,[status(thm)],[c_3641]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_3671,plain,
% 2.08/0.98      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 2.08/0.98      inference(forward_subsumption_resolution,
% 2.08/0.98                [status(thm)],
% 2.08/0.98                [c_3637,c_3660]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_4768,plain,
% 2.08/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.08/0.98      inference(superposition,[status(thm)],[c_1431,c_3671]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1617,plain,
% 2.08/0.98      ( k1_relset_1(sK2,sK3,sK4) != X0
% 2.08/0.98      | k1_xboole_0 != X0
% 2.08/0.98      | k1_xboole_0 = k1_relset_1(sK2,sK3,sK4) ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_914]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2644,plain,
% 2.08/0.98      ( k1_relset_1(sK2,sK3,sK4) != k1_relat_1(X0)
% 2.08/0.98      | k1_xboole_0 = k1_relset_1(sK2,sK3,sK4)
% 2.08/0.98      | k1_xboole_0 != k1_relat_1(X0) ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_1617]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2646,plain,
% 2.08/0.98      ( k1_relset_1(sK2,sK3,sK4) != k1_relat_1(k1_xboole_0)
% 2.08/0.98      | k1_xboole_0 = k1_relset_1(sK2,sK3,sK4)
% 2.08/0.98      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_2644]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_923,plain,
% 2.08/0.98      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 2.08/0.98      theory(equality) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2232,plain,
% 2.08/0.98      ( X0 != sK4 | k1_relat_1(X0) = k1_relat_1(sK4) ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_923]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2234,plain,
% 2.08/0.98      ( k1_relat_1(k1_xboole_0) = k1_relat_1(sK4) | k1_xboole_0 != sK4 ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_2232]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1692,plain,
% 2.08/0.98      ( X0 != X1
% 2.08/0.98      | k1_relset_1(sK2,sK3,sK4) != X1
% 2.08/0.98      | k1_relset_1(sK2,sK3,sK4) = X0 ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_914]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1848,plain,
% 2.08/0.98      ( X0 != k1_relat_1(sK4)
% 2.08/0.98      | k1_relset_1(sK2,sK3,sK4) = X0
% 2.08/0.98      | k1_relset_1(sK2,sK3,sK4) != k1_relat_1(sK4) ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_1692]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2231,plain,
% 2.08/0.98      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(X0)
% 2.08/0.98      | k1_relset_1(sK2,sK3,sK4) != k1_relat_1(sK4)
% 2.08/0.98      | k1_relat_1(X0) != k1_relat_1(sK4) ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_1848]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2233,plain,
% 2.08/0.98      ( k1_relset_1(sK2,sK3,sK4) != k1_relat_1(sK4)
% 2.08/0.98      | k1_relset_1(sK2,sK3,sK4) = k1_relat_1(k1_xboole_0)
% 2.08/0.98      | k1_relat_1(k1_xboole_0) != k1_relat_1(sK4) ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_2231]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2054,plain,
% 2.08/0.98      ( X0 != X1 | X0 = k1_relat_1(X2) | k1_relat_1(X2) != X1 ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_914]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_2055,plain,
% 2.08/0.98      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 2.08/0.98      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 2.08/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_2054]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_18,plain,
% 2.08/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.08/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.08/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_1619,plain,
% 2.08/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.08/0.98      | k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_938,plain,
% 2.08/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 2.08/0.98      inference(instantiation,[status(thm)],[c_913]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(c_21,negated_conjecture,
% 2.08/0.98      ( k1_xboole_0 != k1_relset_1(sK2,sK3,sK4) ),
% 2.08/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.08/0.98  
% 2.08/0.98  cnf(contradiction,plain,
% 2.08/0.98      ( $false ),
% 2.08/0.98      inference(minisat,
% 2.08/0.98                [status(thm)],
% 2.08/0.98                [c_4768,c_3447,c_2646,c_2244,c_2234,c_2233,c_2055,c_1706,
% 2.08/0.98                 c_1619,c_938,c_21,c_22]) ).
% 2.08/0.98  
% 2.08/0.98  
% 2.08/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.08/0.98  
% 2.08/0.98  ------                               Statistics
% 2.08/0.98  
% 2.08/0.98  ------ General
% 2.08/0.98  
% 2.08/0.98  abstr_ref_over_cycles:                  0
% 2.08/0.98  abstr_ref_under_cycles:                 0
% 2.08/0.98  gc_basic_clause_elim:                   0
% 2.08/0.98  forced_gc_time:                         0
% 2.08/0.98  parsing_time:                           0.008
% 2.08/0.98  unif_index_cands_time:                  0.
% 2.08/0.98  unif_index_add_time:                    0.
% 2.08/0.98  orderings_time:                         0.
% 2.08/0.98  out_proof_time:                         0.009
% 2.08/0.98  total_time:                             0.175
% 2.08/0.98  num_of_symbols:                         52
% 2.08/0.98  num_of_terms:                           3972
% 2.08/0.98  
% 2.08/0.98  ------ Preprocessing
% 2.08/0.98  
% 2.08/0.98  num_of_splits:                          0
% 2.08/0.98  num_of_split_atoms:                     0
% 2.08/0.98  num_of_reused_defs:                     0
% 2.08/0.98  num_eq_ax_congr_red:                    31
% 2.08/0.98  num_of_sem_filtered_clauses:            1
% 2.08/0.98  num_of_subtypes:                        0
% 2.08/0.98  monotx_restored_types:                  0
% 2.08/0.98  sat_num_of_epr_types:                   0
% 2.08/0.98  sat_num_of_non_cyclic_types:            0
% 2.08/0.98  sat_guarded_non_collapsed_types:        0
% 2.08/0.98  num_pure_diseq_elim:                    0
% 2.08/0.98  simp_replaced_by:                       0
% 2.08/0.98  res_preprocessed:                       110
% 2.08/0.98  prep_upred:                             0
% 2.08/0.98  prep_unflattend:                        40
% 2.08/0.98  smt_new_axioms:                         0
% 2.08/0.98  pred_elim_cands:                        5
% 2.08/0.98  pred_elim:                              2
% 2.08/0.98  pred_elim_cl:                           3
% 2.08/0.98  pred_elim_cycles:                       8
% 2.08/0.98  merged_defs:                            8
% 2.08/0.98  merged_defs_ncl:                        0
% 2.08/0.98  bin_hyper_res:                          9
% 2.08/0.98  prep_cycles:                            4
% 2.08/0.98  pred_elim_time:                         0.006
% 2.08/0.98  splitting_time:                         0.
% 2.08/0.98  sem_filter_time:                        0.
% 2.08/0.98  monotx_time:                            0.
% 2.08/0.98  subtype_inf_time:                       0.
% 2.08/0.98  
% 2.08/0.98  ------ Problem properties
% 2.08/0.98  
% 2.08/0.98  clauses:                                20
% 2.08/0.98  conjectures:                            3
% 2.08/0.98  epr:                                    1
% 2.08/0.98  horn:                                   18
% 2.08/0.98  ground:                                 2
% 2.08/0.98  unary:                                  3
% 2.08/0.98  binary:                                 9
% 2.08/0.98  lits:                                   45
% 2.08/0.98  lits_eq:                                12
% 2.08/0.98  fd_pure:                                0
% 2.08/0.98  fd_pseudo:                              0
% 2.08/0.98  fd_cond:                                3
% 2.08/0.98  fd_pseudo_cond:                         0
% 2.08/0.98  ac_symbols:                             0
% 2.08/0.98  
% 2.08/0.98  ------ Propositional Solver
% 2.08/0.98  
% 2.08/0.98  prop_solver_calls:                      29
% 2.08/0.98  prop_fast_solver_calls:                 746
% 2.08/0.98  smt_solver_calls:                       0
% 2.08/0.98  smt_fast_solver_calls:                  0
% 2.08/0.98  prop_num_of_clauses:                    1629
% 2.08/0.98  prop_preprocess_simplified:             5063
% 2.08/0.98  prop_fo_subsumed:                       9
% 2.08/0.98  prop_solver_time:                       0.
% 2.08/0.98  smt_solver_time:                        0.
% 2.08/0.98  smt_fast_solver_time:                   0.
% 2.08/0.98  prop_fast_solver_time:                  0.
% 2.08/0.98  prop_unsat_core_time:                   0.
% 2.08/0.98  
% 2.08/0.98  ------ QBF
% 2.08/0.98  
% 2.08/0.98  qbf_q_res:                              0
% 2.08/0.98  qbf_num_tautologies:                    0
% 2.08/0.98  qbf_prep_cycles:                        0
% 2.08/0.98  
% 2.08/0.98  ------ BMC1
% 2.08/0.98  
% 2.08/0.98  bmc1_current_bound:                     -1
% 2.08/0.98  bmc1_last_solved_bound:                 -1
% 2.08/0.98  bmc1_unsat_core_size:                   -1
% 2.08/0.98  bmc1_unsat_core_parents_size:           -1
% 2.08/0.98  bmc1_merge_next_fun:                    0
% 2.08/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.08/0.98  
% 2.08/0.98  ------ Instantiation
% 2.08/0.98  
% 2.08/0.98  inst_num_of_clauses:                    580
% 2.08/0.98  inst_num_in_passive:                    291
% 2.08/0.98  inst_num_in_active:                     286
% 2.08/0.98  inst_num_in_unprocessed:                3
% 2.08/0.98  inst_num_of_loops:                      340
% 2.08/0.98  inst_num_of_learning_restarts:          0
% 2.08/0.98  inst_num_moves_active_passive:          50
% 2.08/0.98  inst_lit_activity:                      0
% 2.08/0.98  inst_lit_activity_moves:                0
% 2.08/0.98  inst_num_tautologies:                   0
% 2.08/0.98  inst_num_prop_implied:                  0
% 2.08/0.98  inst_num_existing_simplified:           0
% 2.08/0.98  inst_num_eq_res_simplified:             0
% 2.08/0.98  inst_num_child_elim:                    0
% 2.08/0.98  inst_num_of_dismatching_blockings:      86
% 2.08/0.98  inst_num_of_non_proper_insts:           413
% 2.08/0.98  inst_num_of_duplicates:                 0
% 2.08/0.98  inst_inst_num_from_inst_to_res:         0
% 2.08/0.98  inst_dismatching_checking_time:         0.
% 2.08/0.98  
% 2.08/0.98  ------ Resolution
% 2.08/0.98  
% 2.08/0.98  res_num_of_clauses:                     0
% 2.08/0.98  res_num_in_passive:                     0
% 2.08/0.98  res_num_in_active:                      0
% 2.08/0.98  res_num_of_loops:                       114
% 2.08/0.98  res_forward_subset_subsumed:            30
% 2.08/0.98  res_backward_subset_subsumed:           0
% 2.08/0.98  res_forward_subsumed:                   0
% 2.08/0.98  res_backward_subsumed:                  0
% 2.08/0.98  res_forward_subsumption_resolution:     0
% 2.08/0.98  res_backward_subsumption_resolution:    0
% 2.08/0.98  res_clause_to_clause_subsumption:       103
% 2.08/0.98  res_orphan_elimination:                 0
% 2.08/0.98  res_tautology_del:                      84
% 2.08/0.98  res_num_eq_res_simplified:              0
% 2.08/0.98  res_num_sel_changes:                    0
% 2.08/0.98  res_moves_from_active_to_pass:          0
% 2.08/0.98  
% 2.08/0.98  ------ Superposition
% 2.08/0.98  
% 2.08/0.98  sup_time_total:                         0.
% 2.08/0.98  sup_time_generating:                    0.
% 2.08/0.98  sup_time_sim_full:                      0.
% 2.08/0.98  sup_time_sim_immed:                     0.
% 2.08/0.98  
% 2.08/0.98  sup_num_of_clauses:                     51
% 2.08/0.98  sup_num_in_active:                      40
% 2.08/0.98  sup_num_in_passive:                     11
% 2.08/0.98  sup_num_of_loops:                       67
% 2.08/0.98  sup_fw_superposition:                   32
% 2.08/0.98  sup_bw_superposition:                   32
% 2.08/0.98  sup_immediate_simplified:               10
% 2.08/0.98  sup_given_eliminated:                   0
% 2.08/0.98  comparisons_done:                       0
% 2.08/0.98  comparisons_avoided:                    0
% 2.08/0.98  
% 2.08/0.98  ------ Simplifications
% 2.08/0.98  
% 2.08/0.98  
% 2.08/0.98  sim_fw_subset_subsumed:                 8
% 2.08/0.98  sim_bw_subset_subsumed:                 2
% 2.08/0.98  sim_fw_subsumed:                        0
% 2.08/0.98  sim_bw_subsumed:                        1
% 2.08/0.98  sim_fw_subsumption_res:                 2
% 2.08/0.98  sim_bw_subsumption_res:                 0
% 2.08/0.98  sim_tautology_del:                      3
% 2.08/0.98  sim_eq_tautology_del:                   1
% 2.08/0.98  sim_eq_res_simp:                        1
% 2.08/0.98  sim_fw_demodulated:                     0
% 2.08/0.98  sim_bw_demodulated:                     27
% 2.08/0.98  sim_light_normalised:                   2
% 2.08/0.98  sim_joinable_taut:                      0
% 2.08/0.98  sim_joinable_simp:                      0
% 2.08/0.98  sim_ac_normalised:                      0
% 2.08/0.98  sim_smt_subsumption:                    0
% 2.08/0.98  
%------------------------------------------------------------------------------
