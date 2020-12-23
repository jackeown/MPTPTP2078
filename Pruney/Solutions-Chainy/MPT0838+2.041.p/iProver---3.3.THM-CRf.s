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
% DateTime   : Thu Dec  3 11:56:33 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 400 expanded)
%              Number of clauses        :   85 ( 155 expanded)
%              Number of leaves         :   21 (  79 expanded)
%              Depth                    :   22
%              Number of atoms          :  394 (1253 expanded)
%              Number of equality atoms :  149 ( 336 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f41])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f39])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k1_relset_1(X0,X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k1_relset_1(X0,X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f46,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
            | ~ m1_subset_1(X3,X1) )
        & k1_xboole_0 != k1_relset_1(X0,X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(sK3,sK4,sK5))
          | ~ m1_subset_1(X3,sK4) )
      & k1_xboole_0 != k1_relset_1(sK3,sK4,sK5)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK3,sK4,sK5))
        | ~ m1_subset_1(X3,sK4) )
    & k1_xboole_0 != k1_relset_1(sK3,sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f34,f46])).

fof(f70,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f72,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK3,sK4,sK5))
      | ~ m1_subset_1(X3,sK4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    k1_xboole_0 != k1_relset_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1760,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1764,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3271,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1760,c_1764])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1761,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1759,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2215,plain,
    ( m1_subset_1(sK1(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1761,c_1759])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1746,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1748,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2575,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1746,c_1748])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1762,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1747,plain,
    ( m1_subset_1(X0,sK4) != iProver_top
    | r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2235,plain,
    ( m1_subset_1(sK1(X0,k2_relset_1(sK3,sK4,sK5)),sK4) != iProver_top
    | r1_xboole_0(X0,k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1747])).

cnf(c_2832,plain,
    ( m1_subset_1(sK1(X0,k2_relat_1(sK5)),sK4) != iProver_top
    | r1_xboole_0(X0,k2_relat_1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2575,c_2235])).

cnf(c_3894,plain,
    ( r1_xboole_0(sK4,k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2215,c_2832])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1763,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4162,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3894,c_1763])).

cnf(c_4231,plain,
    ( k2_relat_1(sK5) = k1_xboole_0
    | r2_hidden(sK2(k2_relat_1(sK5)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1760,c_4162])).

cnf(c_4659,plain,
    ( k2_relat_1(sK5) = k1_xboole_0
    | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3271,c_4231])).

cnf(c_25,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1923,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2041,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1923])).

cnf(c_2042,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2041])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2088,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2089,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2088])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_282,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_12])).

cnf(c_1745,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_2103,plain,
    ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1746,c_1745])).

cnf(c_5159,plain,
    ( k2_relat_1(sK5) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4659,c_25,c_2042,c_2089,c_2103])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1750,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2487,plain,
    ( v4_relat_1(sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1746,c_1750])).

cnf(c_17,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1751,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2642,plain,
    ( k7_relat_1(sK5,sK3) = sK5
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2487,c_1751])).

cnf(c_1951,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2374,plain,
    ( ~ v4_relat_1(sK5,X0)
    | ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,X0) = sK5 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2567,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,sK3) = sK5 ),
    inference(instantiation,[status(thm)],[c_2374])).

cnf(c_3132,plain,
    ( k7_relat_1(sK5,sK3) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2642,c_24,c_1951,c_2041,c_2088,c_2567])).

cnf(c_1758,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2718,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1746,c_1758])).

cnf(c_2949,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2718,c_25,c_2042,c_2089])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1754,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2954,plain,
    ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_2949,c_1754])).

cnf(c_3135,plain,
    ( k9_relat_1(sK5,sK3) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_3132,c_2954])).

cnf(c_16,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1752,plain,
    ( k9_relat_1(X0,X1) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3562,plain,
    ( k2_relat_1(sK5) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK5),sK3) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3135,c_1752])).

cnf(c_3565,plain,
    ( r1_xboole_0(k1_relat_1(sK5),sK3) = iProver_top
    | k2_relat_1(sK5) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3562,c_25,c_2042,c_2089])).

cnf(c_3566,plain,
    ( k2_relat_1(sK5) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK5),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3565])).

cnf(c_5176,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK5),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5159,c_3566])).

cnf(c_5206,plain,
    ( r1_xboole_0(k1_relat_1(sK5),sK3) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5176])).

cnf(c_11448,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5206,c_1763])).

cnf(c_11731,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | r2_hidden(sK2(k1_relat_1(sK5)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1760,c_11448])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != k1_relset_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1326,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1349,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1981,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1327,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1969,plain,
    ( k1_relset_1(sK3,sK4,sK5) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relset_1(sK3,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_2026,plain,
    ( k1_relset_1(sK3,sK4,sK5) != k1_relat_1(sK5)
    | k1_xboole_0 = k1_relset_1(sK3,sK4,sK5)
    | k1_xboole_0 != k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1969])).

cnf(c_2097,plain,
    ( k1_relat_1(sK5) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_2098,plain,
    ( k1_relat_1(sK5) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(sK5)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2097])).

cnf(c_11791,plain,
    ( r2_hidden(sK2(k1_relat_1(sK5)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11731,c_24,c_23,c_1349,c_1981,c_2026,c_2098])).

cnf(c_11796,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | r1_tarski(k1_relat_1(sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3271,c_11791])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3505,plain,
    ( ~ v4_relat_1(sK5,X0)
    | r1_tarski(k1_relat_1(sK5),X0)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_7967,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | r1_tarski(k1_relat_1(sK5),sK3)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_3505])).

cnf(c_7968,plain,
    ( v4_relat_1(sK5,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK5),sK3) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7967])).

cnf(c_1952,plain,
    ( v4_relat_1(sK5,sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1951])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11796,c_7968,c_2098,c_2089,c_2042,c_2026,c_1981,c_1952,c_1349,c_23,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:55:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.36/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.00  
% 2.36/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.36/1.00  
% 2.36/1.00  ------  iProver source info
% 2.36/1.00  
% 2.36/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.36/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.36/1.00  git: non_committed_changes: false
% 2.36/1.00  git: last_make_outside_of_git: false
% 2.36/1.00  
% 2.36/1.00  ------ 
% 2.36/1.00  
% 2.36/1.00  ------ Input Options
% 2.36/1.00  
% 2.36/1.00  --out_options                           all
% 2.36/1.00  --tptp_safe_out                         true
% 2.36/1.00  --problem_path                          ""
% 2.36/1.00  --include_path                          ""
% 2.36/1.00  --clausifier                            res/vclausify_rel
% 2.36/1.00  --clausifier_options                    --mode clausify
% 2.36/1.00  --stdin                                 false
% 2.36/1.00  --stats_out                             all
% 2.36/1.00  
% 2.36/1.00  ------ General Options
% 2.36/1.00  
% 2.36/1.00  --fof                                   false
% 2.36/1.00  --time_out_real                         305.
% 2.36/1.00  --time_out_virtual                      -1.
% 2.36/1.00  --symbol_type_check                     false
% 2.36/1.00  --clausify_out                          false
% 2.36/1.00  --sig_cnt_out                           false
% 2.36/1.00  --trig_cnt_out                          false
% 2.36/1.00  --trig_cnt_out_tolerance                1.
% 2.36/1.00  --trig_cnt_out_sk_spl                   false
% 2.36/1.00  --abstr_cl_out                          false
% 2.36/1.00  
% 2.36/1.00  ------ Global Options
% 2.36/1.00  
% 2.36/1.00  --schedule                              default
% 2.36/1.00  --add_important_lit                     false
% 2.36/1.00  --prop_solver_per_cl                    1000
% 2.36/1.00  --min_unsat_core                        false
% 2.36/1.00  --soft_assumptions                      false
% 2.36/1.00  --soft_lemma_size                       3
% 2.36/1.00  --prop_impl_unit_size                   0
% 2.36/1.00  --prop_impl_unit                        []
% 2.36/1.00  --share_sel_clauses                     true
% 2.36/1.00  --reset_solvers                         false
% 2.36/1.00  --bc_imp_inh                            [conj_cone]
% 2.36/1.00  --conj_cone_tolerance                   3.
% 2.36/1.00  --extra_neg_conj                        none
% 2.36/1.00  --large_theory_mode                     true
% 2.36/1.00  --prolific_symb_bound                   200
% 2.36/1.00  --lt_threshold                          2000
% 2.36/1.00  --clause_weak_htbl                      true
% 2.36/1.00  --gc_record_bc_elim                     false
% 2.36/1.00  
% 2.36/1.00  ------ Preprocessing Options
% 2.36/1.00  
% 2.36/1.00  --preprocessing_flag                    true
% 2.36/1.00  --time_out_prep_mult                    0.1
% 2.36/1.00  --splitting_mode                        input
% 2.36/1.00  --splitting_grd                         true
% 2.36/1.00  --splitting_cvd                         false
% 2.36/1.00  --splitting_cvd_svl                     false
% 2.36/1.00  --splitting_nvd                         32
% 2.36/1.00  --sub_typing                            true
% 2.36/1.00  --prep_gs_sim                           true
% 2.36/1.00  --prep_unflatten                        true
% 2.36/1.00  --prep_res_sim                          true
% 2.36/1.00  --prep_upred                            true
% 2.36/1.00  --prep_sem_filter                       exhaustive
% 2.36/1.00  --prep_sem_filter_out                   false
% 2.36/1.00  --pred_elim                             true
% 2.36/1.00  --res_sim_input                         true
% 2.36/1.00  --eq_ax_congr_red                       true
% 2.36/1.00  --pure_diseq_elim                       true
% 2.36/1.00  --brand_transform                       false
% 2.36/1.00  --non_eq_to_eq                          false
% 2.36/1.00  --prep_def_merge                        true
% 2.36/1.00  --prep_def_merge_prop_impl              false
% 2.36/1.00  --prep_def_merge_mbd                    true
% 2.36/1.00  --prep_def_merge_tr_red                 false
% 2.36/1.00  --prep_def_merge_tr_cl                  false
% 2.36/1.00  --smt_preprocessing                     true
% 2.36/1.00  --smt_ac_axioms                         fast
% 2.36/1.00  --preprocessed_out                      false
% 2.36/1.00  --preprocessed_stats                    false
% 2.36/1.00  
% 2.36/1.00  ------ Abstraction refinement Options
% 2.36/1.00  
% 2.36/1.00  --abstr_ref                             []
% 2.36/1.00  --abstr_ref_prep                        false
% 2.36/1.00  --abstr_ref_until_sat                   false
% 2.36/1.00  --abstr_ref_sig_restrict                funpre
% 2.36/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/1.00  --abstr_ref_under                       []
% 2.36/1.00  
% 2.36/1.00  ------ SAT Options
% 2.36/1.00  
% 2.36/1.00  --sat_mode                              false
% 2.36/1.00  --sat_fm_restart_options                ""
% 2.36/1.00  --sat_gr_def                            false
% 2.36/1.00  --sat_epr_types                         true
% 2.36/1.00  --sat_non_cyclic_types                  false
% 2.36/1.00  --sat_finite_models                     false
% 2.36/1.00  --sat_fm_lemmas                         false
% 2.36/1.00  --sat_fm_prep                           false
% 2.36/1.00  --sat_fm_uc_incr                        true
% 2.36/1.00  --sat_out_model                         small
% 2.36/1.00  --sat_out_clauses                       false
% 2.36/1.00  
% 2.36/1.00  ------ QBF Options
% 2.36/1.00  
% 2.36/1.00  --qbf_mode                              false
% 2.36/1.00  --qbf_elim_univ                         false
% 2.36/1.00  --qbf_dom_inst                          none
% 2.36/1.00  --qbf_dom_pre_inst                      false
% 2.36/1.00  --qbf_sk_in                             false
% 2.36/1.00  --qbf_pred_elim                         true
% 2.36/1.00  --qbf_split                             512
% 2.36/1.00  
% 2.36/1.00  ------ BMC1 Options
% 2.36/1.00  
% 2.36/1.00  --bmc1_incremental                      false
% 2.36/1.00  --bmc1_axioms                           reachable_all
% 2.36/1.00  --bmc1_min_bound                        0
% 2.36/1.00  --bmc1_max_bound                        -1
% 2.36/1.00  --bmc1_max_bound_default                -1
% 2.36/1.00  --bmc1_symbol_reachability              true
% 2.36/1.00  --bmc1_property_lemmas                  false
% 2.36/1.00  --bmc1_k_induction                      false
% 2.36/1.00  --bmc1_non_equiv_states                 false
% 2.36/1.00  --bmc1_deadlock                         false
% 2.36/1.00  --bmc1_ucm                              false
% 2.36/1.00  --bmc1_add_unsat_core                   none
% 2.36/1.00  --bmc1_unsat_core_children              false
% 2.36/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/1.00  --bmc1_out_stat                         full
% 2.36/1.00  --bmc1_ground_init                      false
% 2.36/1.00  --bmc1_pre_inst_next_state              false
% 2.36/1.00  --bmc1_pre_inst_state                   false
% 2.36/1.00  --bmc1_pre_inst_reach_state             false
% 2.36/1.00  --bmc1_out_unsat_core                   false
% 2.36/1.00  --bmc1_aig_witness_out                  false
% 2.36/1.00  --bmc1_verbose                          false
% 2.36/1.00  --bmc1_dump_clauses_tptp                false
% 2.36/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.36/1.00  --bmc1_dump_file                        -
% 2.36/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.36/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.36/1.00  --bmc1_ucm_extend_mode                  1
% 2.36/1.00  --bmc1_ucm_init_mode                    2
% 2.36/1.00  --bmc1_ucm_cone_mode                    none
% 2.36/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.36/1.00  --bmc1_ucm_relax_model                  4
% 2.36/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.36/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/1.00  --bmc1_ucm_layered_model                none
% 2.36/1.00  --bmc1_ucm_max_lemma_size               10
% 2.36/1.00  
% 2.36/1.00  ------ AIG Options
% 2.36/1.00  
% 2.36/1.00  --aig_mode                              false
% 2.36/1.00  
% 2.36/1.00  ------ Instantiation Options
% 2.36/1.00  
% 2.36/1.00  --instantiation_flag                    true
% 2.36/1.00  --inst_sos_flag                         false
% 2.36/1.00  --inst_sos_phase                        true
% 2.36/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/1.00  --inst_lit_sel_side                     num_symb
% 2.36/1.00  --inst_solver_per_active                1400
% 2.36/1.00  --inst_solver_calls_frac                1.
% 2.36/1.00  --inst_passive_queue_type               priority_queues
% 2.36/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/1.00  --inst_passive_queues_freq              [25;2]
% 2.36/1.00  --inst_dismatching                      true
% 2.36/1.00  --inst_eager_unprocessed_to_passive     true
% 2.36/1.00  --inst_prop_sim_given                   true
% 2.36/1.00  --inst_prop_sim_new                     false
% 2.36/1.00  --inst_subs_new                         false
% 2.36/1.00  --inst_eq_res_simp                      false
% 2.36/1.00  --inst_subs_given                       false
% 2.36/1.00  --inst_orphan_elimination               true
% 2.36/1.00  --inst_learning_loop_flag               true
% 2.36/1.00  --inst_learning_start                   3000
% 2.36/1.00  --inst_learning_factor                  2
% 2.36/1.00  --inst_start_prop_sim_after_learn       3
% 2.36/1.00  --inst_sel_renew                        solver
% 2.36/1.00  --inst_lit_activity_flag                true
% 2.36/1.00  --inst_restr_to_given                   false
% 2.36/1.00  --inst_activity_threshold               500
% 2.36/1.00  --inst_out_proof                        true
% 2.36/1.00  
% 2.36/1.00  ------ Resolution Options
% 2.36/1.00  
% 2.36/1.00  --resolution_flag                       true
% 2.36/1.00  --res_lit_sel                           adaptive
% 2.36/1.00  --res_lit_sel_side                      none
% 2.36/1.00  --res_ordering                          kbo
% 2.36/1.00  --res_to_prop_solver                    active
% 2.36/1.00  --res_prop_simpl_new                    false
% 2.36/1.00  --res_prop_simpl_given                  true
% 2.36/1.00  --res_passive_queue_type                priority_queues
% 2.36/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/1.00  --res_passive_queues_freq               [15;5]
% 2.36/1.00  --res_forward_subs                      full
% 2.36/1.00  --res_backward_subs                     full
% 2.36/1.00  --res_forward_subs_resolution           true
% 2.36/1.00  --res_backward_subs_resolution          true
% 2.36/1.00  --res_orphan_elimination                true
% 2.36/1.00  --res_time_limit                        2.
% 2.36/1.00  --res_out_proof                         true
% 2.36/1.00  
% 2.36/1.00  ------ Superposition Options
% 2.36/1.00  
% 2.36/1.00  --superposition_flag                    true
% 2.36/1.00  --sup_passive_queue_type                priority_queues
% 2.36/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.36/1.00  --demod_completeness_check              fast
% 2.36/1.00  --demod_use_ground                      true
% 2.36/1.00  --sup_to_prop_solver                    passive
% 2.36/1.00  --sup_prop_simpl_new                    true
% 2.36/1.00  --sup_prop_simpl_given                  true
% 2.36/1.00  --sup_fun_splitting                     false
% 2.36/1.00  --sup_smt_interval                      50000
% 2.36/1.00  
% 2.36/1.00  ------ Superposition Simplification Setup
% 2.36/1.00  
% 2.36/1.00  --sup_indices_passive                   []
% 2.36/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.00  --sup_full_bw                           [BwDemod]
% 2.36/1.00  --sup_immed_triv                        [TrivRules]
% 2.36/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.00  --sup_immed_bw_main                     []
% 2.36/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.00  
% 2.36/1.00  ------ Combination Options
% 2.36/1.00  
% 2.36/1.00  --comb_res_mult                         3
% 2.36/1.00  --comb_sup_mult                         2
% 2.36/1.00  --comb_inst_mult                        10
% 2.36/1.00  
% 2.36/1.00  ------ Debug Options
% 2.36/1.00  
% 2.36/1.00  --dbg_backtrace                         false
% 2.36/1.00  --dbg_dump_prop_clauses                 false
% 2.36/1.00  --dbg_dump_prop_clauses_file            -
% 2.36/1.00  --dbg_out_stat                          false
% 2.36/1.00  ------ Parsing...
% 2.36/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.36/1.00  
% 2.36/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.36/1.00  
% 2.36/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.36/1.00  
% 2.36/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.36/1.00  ------ Proving...
% 2.36/1.00  ------ Problem Properties 
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  clauses                                 23
% 2.36/1.00  conjectures                             3
% 2.36/1.00  EPR                                     3
% 2.36/1.00  Horn                                    19
% 2.36/1.00  unary                                   3
% 2.36/1.00  binary                                  11
% 2.36/1.00  lits                                    52
% 2.36/1.00  lits eq                                 8
% 2.36/1.00  fd_pure                                 0
% 2.36/1.00  fd_pseudo                               0
% 2.36/1.00  fd_cond                                 1
% 2.36/1.00  fd_pseudo_cond                          0
% 2.36/1.00  AC symbols                              0
% 2.36/1.00  
% 2.36/1.00  ------ Schedule dynamic 5 is on 
% 2.36/1.00  
% 2.36/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  ------ 
% 2.36/1.00  Current options:
% 2.36/1.00  ------ 
% 2.36/1.00  
% 2.36/1.00  ------ Input Options
% 2.36/1.00  
% 2.36/1.00  --out_options                           all
% 2.36/1.00  --tptp_safe_out                         true
% 2.36/1.00  --problem_path                          ""
% 2.36/1.00  --include_path                          ""
% 2.36/1.00  --clausifier                            res/vclausify_rel
% 2.36/1.00  --clausifier_options                    --mode clausify
% 2.36/1.00  --stdin                                 false
% 2.36/1.00  --stats_out                             all
% 2.36/1.00  
% 2.36/1.00  ------ General Options
% 2.36/1.00  
% 2.36/1.00  --fof                                   false
% 2.36/1.00  --time_out_real                         305.
% 2.36/1.00  --time_out_virtual                      -1.
% 2.36/1.00  --symbol_type_check                     false
% 2.36/1.00  --clausify_out                          false
% 2.36/1.00  --sig_cnt_out                           false
% 2.36/1.00  --trig_cnt_out                          false
% 2.36/1.00  --trig_cnt_out_tolerance                1.
% 2.36/1.00  --trig_cnt_out_sk_spl                   false
% 2.36/1.00  --abstr_cl_out                          false
% 2.36/1.00  
% 2.36/1.00  ------ Global Options
% 2.36/1.00  
% 2.36/1.00  --schedule                              default
% 2.36/1.00  --add_important_lit                     false
% 2.36/1.00  --prop_solver_per_cl                    1000
% 2.36/1.00  --min_unsat_core                        false
% 2.36/1.00  --soft_assumptions                      false
% 2.36/1.00  --soft_lemma_size                       3
% 2.36/1.00  --prop_impl_unit_size                   0
% 2.36/1.00  --prop_impl_unit                        []
% 2.36/1.00  --share_sel_clauses                     true
% 2.36/1.00  --reset_solvers                         false
% 2.36/1.00  --bc_imp_inh                            [conj_cone]
% 2.36/1.00  --conj_cone_tolerance                   3.
% 2.36/1.00  --extra_neg_conj                        none
% 2.36/1.00  --large_theory_mode                     true
% 2.36/1.00  --prolific_symb_bound                   200
% 2.36/1.00  --lt_threshold                          2000
% 2.36/1.00  --clause_weak_htbl                      true
% 2.36/1.00  --gc_record_bc_elim                     false
% 2.36/1.00  
% 2.36/1.00  ------ Preprocessing Options
% 2.36/1.00  
% 2.36/1.00  --preprocessing_flag                    true
% 2.36/1.00  --time_out_prep_mult                    0.1
% 2.36/1.00  --splitting_mode                        input
% 2.36/1.00  --splitting_grd                         true
% 2.36/1.00  --splitting_cvd                         false
% 2.36/1.00  --splitting_cvd_svl                     false
% 2.36/1.00  --splitting_nvd                         32
% 2.36/1.00  --sub_typing                            true
% 2.36/1.00  --prep_gs_sim                           true
% 2.36/1.00  --prep_unflatten                        true
% 2.36/1.00  --prep_res_sim                          true
% 2.36/1.00  --prep_upred                            true
% 2.36/1.00  --prep_sem_filter                       exhaustive
% 2.36/1.00  --prep_sem_filter_out                   false
% 2.36/1.00  --pred_elim                             true
% 2.36/1.00  --res_sim_input                         true
% 2.36/1.00  --eq_ax_congr_red                       true
% 2.36/1.00  --pure_diseq_elim                       true
% 2.36/1.00  --brand_transform                       false
% 2.36/1.00  --non_eq_to_eq                          false
% 2.36/1.00  --prep_def_merge                        true
% 2.36/1.00  --prep_def_merge_prop_impl              false
% 2.36/1.00  --prep_def_merge_mbd                    true
% 2.36/1.00  --prep_def_merge_tr_red                 false
% 2.36/1.00  --prep_def_merge_tr_cl                  false
% 2.36/1.00  --smt_preprocessing                     true
% 2.36/1.00  --smt_ac_axioms                         fast
% 2.36/1.00  --preprocessed_out                      false
% 2.36/1.00  --preprocessed_stats                    false
% 2.36/1.00  
% 2.36/1.00  ------ Abstraction refinement Options
% 2.36/1.00  
% 2.36/1.00  --abstr_ref                             []
% 2.36/1.00  --abstr_ref_prep                        false
% 2.36/1.00  --abstr_ref_until_sat                   false
% 2.36/1.00  --abstr_ref_sig_restrict                funpre
% 2.36/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.36/1.00  --abstr_ref_under                       []
% 2.36/1.00  
% 2.36/1.00  ------ SAT Options
% 2.36/1.00  
% 2.36/1.00  --sat_mode                              false
% 2.36/1.00  --sat_fm_restart_options                ""
% 2.36/1.00  --sat_gr_def                            false
% 2.36/1.00  --sat_epr_types                         true
% 2.36/1.00  --sat_non_cyclic_types                  false
% 2.36/1.00  --sat_finite_models                     false
% 2.36/1.00  --sat_fm_lemmas                         false
% 2.36/1.00  --sat_fm_prep                           false
% 2.36/1.00  --sat_fm_uc_incr                        true
% 2.36/1.00  --sat_out_model                         small
% 2.36/1.00  --sat_out_clauses                       false
% 2.36/1.00  
% 2.36/1.00  ------ QBF Options
% 2.36/1.00  
% 2.36/1.00  --qbf_mode                              false
% 2.36/1.00  --qbf_elim_univ                         false
% 2.36/1.00  --qbf_dom_inst                          none
% 2.36/1.00  --qbf_dom_pre_inst                      false
% 2.36/1.00  --qbf_sk_in                             false
% 2.36/1.00  --qbf_pred_elim                         true
% 2.36/1.00  --qbf_split                             512
% 2.36/1.00  
% 2.36/1.00  ------ BMC1 Options
% 2.36/1.00  
% 2.36/1.00  --bmc1_incremental                      false
% 2.36/1.00  --bmc1_axioms                           reachable_all
% 2.36/1.00  --bmc1_min_bound                        0
% 2.36/1.00  --bmc1_max_bound                        -1
% 2.36/1.00  --bmc1_max_bound_default                -1
% 2.36/1.00  --bmc1_symbol_reachability              true
% 2.36/1.00  --bmc1_property_lemmas                  false
% 2.36/1.00  --bmc1_k_induction                      false
% 2.36/1.00  --bmc1_non_equiv_states                 false
% 2.36/1.00  --bmc1_deadlock                         false
% 2.36/1.00  --bmc1_ucm                              false
% 2.36/1.00  --bmc1_add_unsat_core                   none
% 2.36/1.00  --bmc1_unsat_core_children              false
% 2.36/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.36/1.00  --bmc1_out_stat                         full
% 2.36/1.00  --bmc1_ground_init                      false
% 2.36/1.00  --bmc1_pre_inst_next_state              false
% 2.36/1.00  --bmc1_pre_inst_state                   false
% 2.36/1.00  --bmc1_pre_inst_reach_state             false
% 2.36/1.00  --bmc1_out_unsat_core                   false
% 2.36/1.00  --bmc1_aig_witness_out                  false
% 2.36/1.00  --bmc1_verbose                          false
% 2.36/1.00  --bmc1_dump_clauses_tptp                false
% 2.36/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.36/1.00  --bmc1_dump_file                        -
% 2.36/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.36/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.36/1.00  --bmc1_ucm_extend_mode                  1
% 2.36/1.00  --bmc1_ucm_init_mode                    2
% 2.36/1.00  --bmc1_ucm_cone_mode                    none
% 2.36/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.36/1.00  --bmc1_ucm_relax_model                  4
% 2.36/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.36/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.36/1.00  --bmc1_ucm_layered_model                none
% 2.36/1.00  --bmc1_ucm_max_lemma_size               10
% 2.36/1.00  
% 2.36/1.00  ------ AIG Options
% 2.36/1.00  
% 2.36/1.00  --aig_mode                              false
% 2.36/1.00  
% 2.36/1.00  ------ Instantiation Options
% 2.36/1.00  
% 2.36/1.00  --instantiation_flag                    true
% 2.36/1.00  --inst_sos_flag                         false
% 2.36/1.00  --inst_sos_phase                        true
% 2.36/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.36/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.36/1.00  --inst_lit_sel_side                     none
% 2.36/1.00  --inst_solver_per_active                1400
% 2.36/1.00  --inst_solver_calls_frac                1.
% 2.36/1.00  --inst_passive_queue_type               priority_queues
% 2.36/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.36/1.00  --inst_passive_queues_freq              [25;2]
% 2.36/1.00  --inst_dismatching                      true
% 2.36/1.00  --inst_eager_unprocessed_to_passive     true
% 2.36/1.00  --inst_prop_sim_given                   true
% 2.36/1.00  --inst_prop_sim_new                     false
% 2.36/1.00  --inst_subs_new                         false
% 2.36/1.00  --inst_eq_res_simp                      false
% 2.36/1.00  --inst_subs_given                       false
% 2.36/1.00  --inst_orphan_elimination               true
% 2.36/1.00  --inst_learning_loop_flag               true
% 2.36/1.00  --inst_learning_start                   3000
% 2.36/1.00  --inst_learning_factor                  2
% 2.36/1.00  --inst_start_prop_sim_after_learn       3
% 2.36/1.00  --inst_sel_renew                        solver
% 2.36/1.00  --inst_lit_activity_flag                true
% 2.36/1.00  --inst_restr_to_given                   false
% 2.36/1.00  --inst_activity_threshold               500
% 2.36/1.00  --inst_out_proof                        true
% 2.36/1.00  
% 2.36/1.00  ------ Resolution Options
% 2.36/1.00  
% 2.36/1.00  --resolution_flag                       false
% 2.36/1.00  --res_lit_sel                           adaptive
% 2.36/1.00  --res_lit_sel_side                      none
% 2.36/1.00  --res_ordering                          kbo
% 2.36/1.00  --res_to_prop_solver                    active
% 2.36/1.00  --res_prop_simpl_new                    false
% 2.36/1.00  --res_prop_simpl_given                  true
% 2.36/1.00  --res_passive_queue_type                priority_queues
% 2.36/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.36/1.00  --res_passive_queues_freq               [15;5]
% 2.36/1.00  --res_forward_subs                      full
% 2.36/1.00  --res_backward_subs                     full
% 2.36/1.00  --res_forward_subs_resolution           true
% 2.36/1.00  --res_backward_subs_resolution          true
% 2.36/1.00  --res_orphan_elimination                true
% 2.36/1.00  --res_time_limit                        2.
% 2.36/1.00  --res_out_proof                         true
% 2.36/1.00  
% 2.36/1.00  ------ Superposition Options
% 2.36/1.00  
% 2.36/1.00  --superposition_flag                    true
% 2.36/1.00  --sup_passive_queue_type                priority_queues
% 2.36/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.36/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.36/1.00  --demod_completeness_check              fast
% 2.36/1.00  --demod_use_ground                      true
% 2.36/1.00  --sup_to_prop_solver                    passive
% 2.36/1.00  --sup_prop_simpl_new                    true
% 2.36/1.00  --sup_prop_simpl_given                  true
% 2.36/1.00  --sup_fun_splitting                     false
% 2.36/1.00  --sup_smt_interval                      50000
% 2.36/1.00  
% 2.36/1.00  ------ Superposition Simplification Setup
% 2.36/1.00  
% 2.36/1.00  --sup_indices_passive                   []
% 2.36/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.36/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.36/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.00  --sup_full_bw                           [BwDemod]
% 2.36/1.00  --sup_immed_triv                        [TrivRules]
% 2.36/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.36/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.00  --sup_immed_bw_main                     []
% 2.36/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.36/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.36/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.36/1.00  
% 2.36/1.00  ------ Combination Options
% 2.36/1.00  
% 2.36/1.00  --comb_res_mult                         3
% 2.36/1.00  --comb_sup_mult                         2
% 2.36/1.00  --comb_inst_mult                        10
% 2.36/1.00  
% 2.36/1.00  ------ Debug Options
% 2.36/1.00  
% 2.36/1.00  --dbg_backtrace                         false
% 2.36/1.00  --dbg_dump_prop_clauses                 false
% 2.36/1.00  --dbg_dump_prop_clauses_file            -
% 2.36/1.00  --dbg_out_stat                          false
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  ------ Proving...
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  % SZS status Theorem for theBenchmark.p
% 2.36/1.00  
% 2.36/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.36/1.00  
% 2.36/1.00  fof(f3,axiom,(
% 2.36/1.00    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f21,plain,(
% 2.36/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.36/1.00    inference(ennf_transformation,[],[f3])).
% 2.36/1.00  
% 2.36/1.00  fof(f41,plain,(
% 2.36/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.36/1.00    introduced(choice_axiom,[])).
% 2.36/1.00  
% 2.36/1.00  fof(f42,plain,(
% 2.36/1.00    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 2.36/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f41])).
% 2.36/1.00  
% 2.36/1.00  fof(f54,plain,(
% 2.36/1.00    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 2.36/1.00    inference(cnf_transformation,[],[f42])).
% 2.36/1.00  
% 2.36/1.00  fof(f1,axiom,(
% 2.36/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f19,plain,(
% 2.36/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.36/1.00    inference(ennf_transformation,[],[f1])).
% 2.36/1.00  
% 2.36/1.00  fof(f35,plain,(
% 2.36/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.36/1.00    inference(nnf_transformation,[],[f19])).
% 2.36/1.00  
% 2.36/1.00  fof(f36,plain,(
% 2.36/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.36/1.00    inference(rectify,[],[f35])).
% 2.36/1.00  
% 2.36/1.00  fof(f37,plain,(
% 2.36/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.36/1.00    introduced(choice_axiom,[])).
% 2.36/1.00  
% 2.36/1.00  fof(f38,plain,(
% 2.36/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.36/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 2.36/1.00  
% 2.36/1.00  fof(f48,plain,(
% 2.36/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f38])).
% 2.36/1.00  
% 2.36/1.00  fof(f2,axiom,(
% 2.36/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f17,plain,(
% 2.36/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.36/1.00    inference(rectify,[],[f2])).
% 2.36/1.00  
% 2.36/1.00  fof(f20,plain,(
% 2.36/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.36/1.00    inference(ennf_transformation,[],[f17])).
% 2.36/1.00  
% 2.36/1.00  fof(f39,plain,(
% 2.36/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.36/1.00    introduced(choice_axiom,[])).
% 2.36/1.00  
% 2.36/1.00  fof(f40,plain,(
% 2.36/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.36/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f39])).
% 2.36/1.00  
% 2.36/1.00  fof(f51,plain,(
% 2.36/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f40])).
% 2.36/1.00  
% 2.36/1.00  fof(f4,axiom,(
% 2.36/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f22,plain,(
% 2.36/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.36/1.00    inference(ennf_transformation,[],[f4])).
% 2.36/1.00  
% 2.36/1.00  fof(f55,plain,(
% 2.36/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f22])).
% 2.36/1.00  
% 2.36/1.00  fof(f15,conjecture,(
% 2.36/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f16,negated_conjecture,(
% 2.36/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 2.36/1.00    inference(negated_conjecture,[],[f15])).
% 2.36/1.00  
% 2.36/1.00  fof(f18,plain,(
% 2.36/1.00    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))),
% 2.36/1.00    inference(pure_predicate_removal,[],[f16])).
% 2.36/1.00  
% 2.36/1.00  fof(f33,plain,(
% 2.36/1.00    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.36/1.00    inference(ennf_transformation,[],[f18])).
% 2.36/1.00  
% 2.36/1.00  fof(f34,plain,(
% 2.36/1.00    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.36/1.00    inference(flattening,[],[f33])).
% 2.36/1.00  
% 2.36/1.00  fof(f46,plain,(
% 2.36/1.00    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(sK3,sK4,sK5)) | ~m1_subset_1(X3,sK4)) & k1_xboole_0 != k1_relset_1(sK3,sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))))),
% 2.36/1.00    introduced(choice_axiom,[])).
% 2.36/1.00  
% 2.36/1.00  fof(f47,plain,(
% 2.36/1.00    ! [X3] : (~r2_hidden(X3,k2_relset_1(sK3,sK4,sK5)) | ~m1_subset_1(X3,sK4)) & k1_xboole_0 != k1_relset_1(sK3,sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.36/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f34,f46])).
% 2.36/1.00  
% 2.36/1.00  fof(f70,plain,(
% 2.36/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 2.36/1.00    inference(cnf_transformation,[],[f47])).
% 2.36/1.00  
% 2.36/1.00  fof(f14,axiom,(
% 2.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f32,plain,(
% 2.36/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.36/1.00    inference(ennf_transformation,[],[f14])).
% 2.36/1.00  
% 2.36/1.00  fof(f69,plain,(
% 2.36/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.36/1.00    inference(cnf_transformation,[],[f32])).
% 2.36/1.00  
% 2.36/1.00  fof(f52,plain,(
% 2.36/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f40])).
% 2.36/1.00  
% 2.36/1.00  fof(f72,plain,(
% 2.36/1.00    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK3,sK4,sK5)) | ~m1_subset_1(X3,sK4)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f47])).
% 2.36/1.00  
% 2.36/1.00  fof(f53,plain,(
% 2.36/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f40])).
% 2.36/1.00  
% 2.36/1.00  fof(f5,axiom,(
% 2.36/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f23,plain,(
% 2.36/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.36/1.00    inference(ennf_transformation,[],[f5])).
% 2.36/1.00  
% 2.36/1.00  fof(f56,plain,(
% 2.36/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f23])).
% 2.36/1.00  
% 2.36/1.00  fof(f8,axiom,(
% 2.36/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f61,plain,(
% 2.36/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.36/1.00    inference(cnf_transformation,[],[f8])).
% 2.36/1.00  
% 2.36/1.00  fof(f12,axiom,(
% 2.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f30,plain,(
% 2.36/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.36/1.00    inference(ennf_transformation,[],[f12])).
% 2.36/1.00  
% 2.36/1.00  fof(f67,plain,(
% 2.36/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.36/1.00    inference(cnf_transformation,[],[f30])).
% 2.36/1.00  
% 2.36/1.00  fof(f7,axiom,(
% 2.36/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f25,plain,(
% 2.36/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.36/1.00    inference(ennf_transformation,[],[f7])).
% 2.36/1.00  
% 2.36/1.00  fof(f44,plain,(
% 2.36/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.36/1.00    inference(nnf_transformation,[],[f25])).
% 2.36/1.00  
% 2.36/1.00  fof(f59,plain,(
% 2.36/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f44])).
% 2.36/1.00  
% 2.36/1.00  fof(f66,plain,(
% 2.36/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.36/1.00    inference(cnf_transformation,[],[f30])).
% 2.36/1.00  
% 2.36/1.00  fof(f11,axiom,(
% 2.36/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f28,plain,(
% 2.36/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.36/1.00    inference(ennf_transformation,[],[f11])).
% 2.36/1.00  
% 2.36/1.00  fof(f29,plain,(
% 2.36/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.36/1.00    inference(flattening,[],[f28])).
% 2.36/1.00  
% 2.36/1.00  fof(f65,plain,(
% 2.36/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f29])).
% 2.36/1.00  
% 2.36/1.00  fof(f9,axiom,(
% 2.36/1.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f26,plain,(
% 2.36/1.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.36/1.00    inference(ennf_transformation,[],[f9])).
% 2.36/1.00  
% 2.36/1.00  fof(f62,plain,(
% 2.36/1.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f26])).
% 2.36/1.00  
% 2.36/1.00  fof(f10,axiom,(
% 2.36/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f27,plain,(
% 2.36/1.00    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.36/1.00    inference(ennf_transformation,[],[f10])).
% 2.36/1.00  
% 2.36/1.00  fof(f45,plain,(
% 2.36/1.00    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.36/1.00    inference(nnf_transformation,[],[f27])).
% 2.36/1.00  
% 2.36/1.00  fof(f63,plain,(
% 2.36/1.00    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f45])).
% 2.36/1.00  
% 2.36/1.00  fof(f71,plain,(
% 2.36/1.00    k1_xboole_0 != k1_relset_1(sK3,sK4,sK5)),
% 2.36/1.00    inference(cnf_transformation,[],[f47])).
% 2.36/1.00  
% 2.36/1.00  fof(f13,axiom,(
% 2.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f31,plain,(
% 2.36/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.36/1.00    inference(ennf_transformation,[],[f13])).
% 2.36/1.00  
% 2.36/1.00  fof(f68,plain,(
% 2.36/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.36/1.00    inference(cnf_transformation,[],[f31])).
% 2.36/1.00  
% 2.36/1.00  fof(f6,axiom,(
% 2.36/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.36/1.00  
% 2.36/1.00  fof(f24,plain,(
% 2.36/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.36/1.00    inference(ennf_transformation,[],[f6])).
% 2.36/1.00  
% 2.36/1.00  fof(f43,plain,(
% 2.36/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.36/1.00    inference(nnf_transformation,[],[f24])).
% 2.36/1.00  
% 2.36/1.00  fof(f57,plain,(
% 2.36/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.36/1.00    inference(cnf_transformation,[],[f43])).
% 2.36/1.00  
% 2.36/1.00  cnf(c_6,plain,
% 2.36/1.00      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 2.36/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1760,plain,
% 2.36/1.00      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2,plain,
% 2.36/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.36/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1764,plain,
% 2.36/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.36/1.00      | r2_hidden(X0,X2) = iProver_top
% 2.36/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3271,plain,
% 2.36/1.00      ( k1_xboole_0 = X0
% 2.36/1.00      | r2_hidden(sK2(X0),X1) = iProver_top
% 2.36/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1760,c_1764]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_5,plain,
% 2.36/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1761,plain,
% 2.36/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 2.36/1.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_7,plain,
% 2.36/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.36/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1759,plain,
% 2.36/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 2.36/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2215,plain,
% 2.36/1.00      ( m1_subset_1(sK1(X0,X1),X0) = iProver_top
% 2.36/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1761,c_1759]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_24,negated_conjecture,
% 2.36/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.36/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1746,plain,
% 2.36/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_21,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1748,plain,
% 2.36/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.36/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2575,plain,
% 2.36/1.00      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1746,c_1748]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_4,plain,
% 2.36/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 2.36/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1762,plain,
% 2.36/1.00      ( r1_xboole_0(X0,X1) = iProver_top
% 2.36/1.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_22,negated_conjecture,
% 2.36/1.00      ( ~ m1_subset_1(X0,sK4)
% 2.36/1.00      | ~ r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) ),
% 2.36/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1747,plain,
% 2.36/1.00      ( m1_subset_1(X0,sK4) != iProver_top
% 2.36/1.00      | r2_hidden(X0,k2_relset_1(sK3,sK4,sK5)) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2235,plain,
% 2.36/1.00      ( m1_subset_1(sK1(X0,k2_relset_1(sK3,sK4,sK5)),sK4) != iProver_top
% 2.36/1.00      | r1_xboole_0(X0,k2_relset_1(sK3,sK4,sK5)) = iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1762,c_1747]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2832,plain,
% 2.36/1.00      ( m1_subset_1(sK1(X0,k2_relat_1(sK5)),sK4) != iProver_top
% 2.36/1.00      | r1_xboole_0(X0,k2_relat_1(sK5)) = iProver_top ),
% 2.36/1.00      inference(demodulation,[status(thm)],[c_2575,c_2235]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3894,plain,
% 2.36/1.00      ( r1_xboole_0(sK4,k2_relat_1(sK5)) = iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_2215,c_2832]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3,plain,
% 2.36/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1763,plain,
% 2.36/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 2.36/1.00      | r2_hidden(X2,X1) != iProver_top
% 2.36/1.00      | r2_hidden(X2,X0) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_4162,plain,
% 2.36/1.00      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 2.36/1.00      | r2_hidden(X0,sK4) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_3894,c_1763]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_4231,plain,
% 2.36/1.00      ( k2_relat_1(sK5) = k1_xboole_0
% 2.36/1.00      | r2_hidden(sK2(k2_relat_1(sK5)),sK4) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1760,c_4162]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_4659,plain,
% 2.36/1.00      ( k2_relat_1(sK5) = k1_xboole_0
% 2.36/1.00      | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_3271,c_4231]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_25,plain,
% 2.36/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_8,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.36/1.00      | ~ v1_relat_1(X1)
% 2.36/1.00      | v1_relat_1(X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1923,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/1.00      | v1_relat_1(X0)
% 2.36/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2041,plain,
% 2.36/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.36/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 2.36/1.00      | v1_relat_1(sK5) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_1923]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2042,plain,
% 2.36/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 2.36/1.00      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 2.36/1.00      | v1_relat_1(sK5) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_2041]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_13,plain,
% 2.36/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.36/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2088,plain,
% 2.36/1.00      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2089,plain,
% 2.36/1.00      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_2088]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_18,plain,
% 2.36/1.00      ( v5_relat_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.36/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_12,plain,
% 2.36/1.00      ( ~ v5_relat_1(X0,X1)
% 2.36/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 2.36/1.00      | ~ v1_relat_1(X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_282,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 2.36/1.00      | ~ v1_relat_1(X0) ),
% 2.36/1.00      inference(resolution,[status(thm)],[c_18,c_12]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1745,plain,
% 2.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.36/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 2.36/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2103,plain,
% 2.36/1.00      ( r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
% 2.36/1.00      | v1_relat_1(sK5) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1746,c_1745]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_5159,plain,
% 2.36/1.00      ( k2_relat_1(sK5) = k1_xboole_0 ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_4659,c_25,c_2042,c_2089,c_2103]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_19,plain,
% 2.36/1.00      ( v4_relat_1(X0,X1)
% 2.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.36/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1750,plain,
% 2.36/1.00      ( v4_relat_1(X0,X1) = iProver_top
% 2.36/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2487,plain,
% 2.36/1.00      ( v4_relat_1(sK5,sK3) = iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1746,c_1750]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_17,plain,
% 2.36/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.36/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1751,plain,
% 2.36/1.00      ( k7_relat_1(X0,X1) = X0
% 2.36/1.00      | v4_relat_1(X0,X1) != iProver_top
% 2.36/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2642,plain,
% 2.36/1.00      ( k7_relat_1(sK5,sK3) = sK5 | v1_relat_1(sK5) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_2487,c_1751]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1951,plain,
% 2.36/1.00      ( v4_relat_1(sK5,sK3)
% 2.36/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2374,plain,
% 2.36/1.00      ( ~ v4_relat_1(sK5,X0)
% 2.36/1.00      | ~ v1_relat_1(sK5)
% 2.36/1.00      | k7_relat_1(sK5,X0) = sK5 ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2567,plain,
% 2.36/1.00      ( ~ v4_relat_1(sK5,sK3)
% 2.36/1.00      | ~ v1_relat_1(sK5)
% 2.36/1.00      | k7_relat_1(sK5,sK3) = sK5 ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_2374]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3132,plain,
% 2.36/1.00      ( k7_relat_1(sK5,sK3) = sK5 ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_2642,c_24,c_1951,c_2041,c_2088,c_2567]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1758,plain,
% 2.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.36/1.00      | v1_relat_1(X1) != iProver_top
% 2.36/1.00      | v1_relat_1(X0) = iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2718,plain,
% 2.36/1.00      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 2.36/1.00      | v1_relat_1(sK5) = iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1746,c_1758]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2949,plain,
% 2.36/1.00      ( v1_relat_1(sK5) = iProver_top ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_2718,c_25,c_2042,c_2089]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_14,plain,
% 2.36/1.00      ( ~ v1_relat_1(X0)
% 2.36/1.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.36/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1754,plain,
% 2.36/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.36/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2954,plain,
% 2.36/1.00      ( k2_relat_1(k7_relat_1(sK5,X0)) = k9_relat_1(sK5,X0) ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_2949,c_1754]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3135,plain,
% 2.36/1.00      ( k9_relat_1(sK5,sK3) = k2_relat_1(sK5) ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_3132,c_2954]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_16,plain,
% 2.36/1.00      ( r1_xboole_0(k1_relat_1(X0),X1)
% 2.36/1.00      | ~ v1_relat_1(X0)
% 2.36/1.00      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 2.36/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1752,plain,
% 2.36/1.00      ( k9_relat_1(X0,X1) != k1_xboole_0
% 2.36/1.00      | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
% 2.36/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3562,plain,
% 2.36/1.00      ( k2_relat_1(sK5) != k1_xboole_0
% 2.36/1.00      | r1_xboole_0(k1_relat_1(sK5),sK3) = iProver_top
% 2.36/1.00      | v1_relat_1(sK5) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_3135,c_1752]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3565,plain,
% 2.36/1.00      ( r1_xboole_0(k1_relat_1(sK5),sK3) = iProver_top
% 2.36/1.00      | k2_relat_1(sK5) != k1_xboole_0 ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_3562,c_25,c_2042,c_2089]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3566,plain,
% 2.36/1.00      ( k2_relat_1(sK5) != k1_xboole_0
% 2.36/1.00      | r1_xboole_0(k1_relat_1(sK5),sK3) = iProver_top ),
% 2.36/1.00      inference(renaming,[status(thm)],[c_3565]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_5176,plain,
% 2.36/1.00      ( k1_xboole_0 != k1_xboole_0
% 2.36/1.00      | r1_xboole_0(k1_relat_1(sK5),sK3) = iProver_top ),
% 2.36/1.00      inference(demodulation,[status(thm)],[c_5159,c_3566]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_5206,plain,
% 2.36/1.00      ( r1_xboole_0(k1_relat_1(sK5),sK3) = iProver_top ),
% 2.36/1.00      inference(equality_resolution_simp,[status(thm)],[c_5176]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_11448,plain,
% 2.36/1.00      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 2.36/1.00      | r2_hidden(X0,sK3) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_5206,c_1763]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_11731,plain,
% 2.36/1.00      ( k1_relat_1(sK5) = k1_xboole_0
% 2.36/1.00      | r2_hidden(sK2(k1_relat_1(sK5)),sK3) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_1760,c_11448]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_23,negated_conjecture,
% 2.36/1.00      ( k1_xboole_0 != k1_relset_1(sK3,sK4,sK5) ),
% 2.36/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1326,plain,( X0 = X0 ),theory(equality) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1349,plain,
% 2.36/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_1326]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_20,plain,
% 2.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.36/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1981,plain,
% 2.36/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 2.36/1.00      | k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1327,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1969,plain,
% 2.36/1.00      ( k1_relset_1(sK3,sK4,sK5) != X0
% 2.36/1.00      | k1_xboole_0 != X0
% 2.36/1.00      | k1_xboole_0 = k1_relset_1(sK3,sK4,sK5) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_1327]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2026,plain,
% 2.36/1.00      ( k1_relset_1(sK3,sK4,sK5) != k1_relat_1(sK5)
% 2.36/1.00      | k1_xboole_0 = k1_relset_1(sK3,sK4,sK5)
% 2.36/1.00      | k1_xboole_0 != k1_relat_1(sK5) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_1969]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2097,plain,
% 2.36/1.00      ( k1_relat_1(sK5) != X0
% 2.36/1.00      | k1_xboole_0 != X0
% 2.36/1.00      | k1_xboole_0 = k1_relat_1(sK5) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_1327]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_2098,plain,
% 2.36/1.00      ( k1_relat_1(sK5) != k1_xboole_0
% 2.36/1.00      | k1_xboole_0 = k1_relat_1(sK5)
% 2.36/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_2097]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_11791,plain,
% 2.36/1.00      ( r2_hidden(sK2(k1_relat_1(sK5)),sK3) != iProver_top ),
% 2.36/1.00      inference(global_propositional_subsumption,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_11731,c_24,c_23,c_1349,c_1981,c_2026,c_2098]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_11796,plain,
% 2.36/1.00      ( k1_relat_1(sK5) = k1_xboole_0
% 2.36/1.00      | r1_tarski(k1_relat_1(sK5),sK3) != iProver_top ),
% 2.36/1.00      inference(superposition,[status(thm)],[c_3271,c_11791]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_10,plain,
% 2.36/1.00      ( ~ v4_relat_1(X0,X1)
% 2.36/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 2.36/1.00      | ~ v1_relat_1(X0) ),
% 2.36/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_3505,plain,
% 2.36/1.00      ( ~ v4_relat_1(sK5,X0)
% 2.36/1.00      | r1_tarski(k1_relat_1(sK5),X0)
% 2.36/1.00      | ~ v1_relat_1(sK5) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_7967,plain,
% 2.36/1.00      ( ~ v4_relat_1(sK5,sK3)
% 2.36/1.00      | r1_tarski(k1_relat_1(sK5),sK3)
% 2.36/1.00      | ~ v1_relat_1(sK5) ),
% 2.36/1.00      inference(instantiation,[status(thm)],[c_3505]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_7968,plain,
% 2.36/1.00      ( v4_relat_1(sK5,sK3) != iProver_top
% 2.36/1.00      | r1_tarski(k1_relat_1(sK5),sK3) = iProver_top
% 2.36/1.00      | v1_relat_1(sK5) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_7967]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(c_1952,plain,
% 2.36/1.00      ( v4_relat_1(sK5,sK3) = iProver_top
% 2.36/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 2.36/1.00      inference(predicate_to_equality,[status(thm)],[c_1951]) ).
% 2.36/1.00  
% 2.36/1.00  cnf(contradiction,plain,
% 2.36/1.00      ( $false ),
% 2.36/1.00      inference(minisat,
% 2.36/1.00                [status(thm)],
% 2.36/1.00                [c_11796,c_7968,c_2098,c_2089,c_2042,c_2026,c_1981,
% 2.36/1.00                 c_1952,c_1349,c_23,c_25,c_24]) ).
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.36/1.00  
% 2.36/1.00  ------                               Statistics
% 2.36/1.00  
% 2.36/1.00  ------ General
% 2.36/1.00  
% 2.36/1.00  abstr_ref_over_cycles:                  0
% 2.36/1.00  abstr_ref_under_cycles:                 0
% 2.36/1.00  gc_basic_clause_elim:                   0
% 2.36/1.00  forced_gc_time:                         0
% 2.36/1.00  parsing_time:                           0.006
% 2.36/1.00  unif_index_cands_time:                  0.
% 2.36/1.00  unif_index_add_time:                    0.
% 2.36/1.00  orderings_time:                         0.
% 2.36/1.00  out_proof_time:                         0.011
% 2.36/1.00  total_time:                             0.285
% 2.36/1.00  num_of_symbols:                         53
% 2.36/1.00  num_of_terms:                           8172
% 2.36/1.00  
% 2.36/1.00  ------ Preprocessing
% 2.36/1.00  
% 2.36/1.00  num_of_splits:                          0
% 2.36/1.00  num_of_split_atoms:                     0
% 2.36/1.00  num_of_reused_defs:                     0
% 2.36/1.00  num_eq_ax_congr_red:                    44
% 2.36/1.00  num_of_sem_filtered_clauses:            1
% 2.36/1.00  num_of_subtypes:                        0
% 2.36/1.00  monotx_restored_types:                  0
% 2.36/1.00  sat_num_of_epr_types:                   0
% 2.36/1.00  sat_num_of_non_cyclic_types:            0
% 2.36/1.00  sat_guarded_non_collapsed_types:        0
% 2.36/1.00  num_pure_diseq_elim:                    0
% 2.36/1.00  simp_replaced_by:                       0
% 2.36/1.00  res_preprocessed:                       119
% 2.36/1.00  prep_upred:                             0
% 2.36/1.00  prep_unflattend:                        74
% 2.36/1.00  smt_new_axioms:                         0
% 2.36/1.00  pred_elim_cands:                        6
% 2.36/1.00  pred_elim:                              1
% 2.36/1.00  pred_elim_cl:                           2
% 2.36/1.00  pred_elim_cycles:                       9
% 2.36/1.00  merged_defs:                            0
% 2.36/1.00  merged_defs_ncl:                        0
% 2.36/1.00  bin_hyper_res:                          0
% 2.36/1.00  prep_cycles:                            4
% 2.36/1.00  pred_elim_time:                         0.008
% 2.36/1.00  splitting_time:                         0.
% 2.36/1.00  sem_filter_time:                        0.
% 2.36/1.00  monotx_time:                            0.
% 2.36/1.00  subtype_inf_time:                       0.
% 2.36/1.00  
% 2.36/1.00  ------ Problem properties
% 2.36/1.00  
% 2.36/1.00  clauses:                                23
% 2.36/1.00  conjectures:                            3
% 2.36/1.00  epr:                                    3
% 2.36/1.00  horn:                                   19
% 2.36/1.00  ground:                                 2
% 2.36/1.00  unary:                                  3
% 2.36/1.00  binary:                                 11
% 2.36/1.00  lits:                                   52
% 2.36/1.00  lits_eq:                                8
% 2.36/1.00  fd_pure:                                0
% 2.36/1.00  fd_pseudo:                              0
% 2.36/1.00  fd_cond:                                1
% 2.36/1.00  fd_pseudo_cond:                         0
% 2.36/1.00  ac_symbols:                             0
% 2.36/1.00  
% 2.36/1.00  ------ Propositional Solver
% 2.36/1.00  
% 2.36/1.00  prop_solver_calls:                      31
% 2.36/1.00  prop_fast_solver_calls:                 1132
% 2.36/1.00  smt_solver_calls:                       0
% 2.36/1.00  smt_fast_solver_calls:                  0
% 2.36/1.00  prop_num_of_clauses:                    4167
% 2.36/1.00  prop_preprocess_simplified:             8425
% 2.36/1.00  prop_fo_subsumed:                       10
% 2.36/1.00  prop_solver_time:                       0.
% 2.36/1.00  smt_solver_time:                        0.
% 2.36/1.00  smt_fast_solver_time:                   0.
% 2.36/1.00  prop_fast_solver_time:                  0.
% 2.36/1.00  prop_unsat_core_time:                   0.
% 2.36/1.00  
% 2.36/1.00  ------ QBF
% 2.36/1.00  
% 2.36/1.00  qbf_q_res:                              0
% 2.36/1.00  qbf_num_tautologies:                    0
% 2.36/1.00  qbf_prep_cycles:                        0
% 2.36/1.00  
% 2.36/1.00  ------ BMC1
% 2.36/1.00  
% 2.36/1.00  bmc1_current_bound:                     -1
% 2.36/1.00  bmc1_last_solved_bound:                 -1
% 2.36/1.00  bmc1_unsat_core_size:                   -1
% 2.36/1.00  bmc1_unsat_core_parents_size:           -1
% 2.36/1.00  bmc1_merge_next_fun:                    0
% 2.36/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.36/1.00  
% 2.36/1.00  ------ Instantiation
% 2.36/1.00  
% 2.36/1.00  inst_num_of_clauses:                    1137
% 2.36/1.00  inst_num_in_passive:                    463
% 2.36/1.00  inst_num_in_active:                     609
% 2.36/1.00  inst_num_in_unprocessed:                66
% 2.36/1.00  inst_num_of_loops:                      820
% 2.36/1.00  inst_num_of_learning_restarts:          0
% 2.36/1.00  inst_num_moves_active_passive:          206
% 2.36/1.00  inst_lit_activity:                      0
% 2.36/1.00  inst_lit_activity_moves:                0
% 2.36/1.00  inst_num_tautologies:                   0
% 2.36/1.00  inst_num_prop_implied:                  0
% 2.36/1.00  inst_num_existing_simplified:           0
% 2.36/1.00  inst_num_eq_res_simplified:             0
% 2.36/1.00  inst_num_child_elim:                    0
% 2.36/1.00  inst_num_of_dismatching_blockings:      514
% 2.36/1.00  inst_num_of_non_proper_insts:           1311
% 2.36/1.00  inst_num_of_duplicates:                 0
% 2.36/1.00  inst_inst_num_from_inst_to_res:         0
% 2.36/1.00  inst_dismatching_checking_time:         0.
% 2.36/1.00  
% 2.36/1.00  ------ Resolution
% 2.36/1.00  
% 2.36/1.00  res_num_of_clauses:                     0
% 2.36/1.00  res_num_in_passive:                     0
% 2.36/1.00  res_num_in_active:                      0
% 2.36/1.00  res_num_of_loops:                       123
% 2.36/1.00  res_forward_subset_subsumed:            91
% 2.36/1.00  res_backward_subset_subsumed:           2
% 2.36/1.00  res_forward_subsumed:                   0
% 2.36/1.00  res_backward_subsumed:                  0
% 2.36/1.00  res_forward_subsumption_resolution:     0
% 2.36/1.00  res_backward_subsumption_resolution:    0
% 2.36/1.00  res_clause_to_clause_subsumption:       880
% 2.36/1.00  res_orphan_elimination:                 0
% 2.36/1.00  res_tautology_del:                      153
% 2.36/1.00  res_num_eq_res_simplified:              0
% 2.36/1.00  res_num_sel_changes:                    0
% 2.36/1.00  res_moves_from_active_to_pass:          0
% 2.36/1.00  
% 2.36/1.00  ------ Superposition
% 2.36/1.00  
% 2.36/1.00  sup_time_total:                         0.
% 2.36/1.00  sup_time_generating:                    0.
% 2.36/1.00  sup_time_sim_full:                      0.
% 2.36/1.00  sup_time_sim_immed:                     0.
% 2.36/1.00  
% 2.36/1.00  sup_num_of_clauses:                     241
% 2.36/1.00  sup_num_in_active:                      130
% 2.36/1.00  sup_num_in_passive:                     111
% 2.36/1.00  sup_num_of_loops:                       163
% 2.36/1.00  sup_fw_superposition:                   168
% 2.36/1.00  sup_bw_superposition:                   142
% 2.36/1.00  sup_immediate_simplified:               16
% 2.36/1.00  sup_given_eliminated:                   0
% 2.36/1.00  comparisons_done:                       0
% 2.36/1.00  comparisons_avoided:                    16
% 2.36/1.00  
% 2.36/1.00  ------ Simplifications
% 2.36/1.00  
% 2.36/1.00  
% 2.36/1.00  sim_fw_subset_subsumed:                 10
% 2.36/1.00  sim_bw_subset_subsumed:                 13
% 2.36/1.00  sim_fw_subsumed:                        3
% 2.36/1.00  sim_bw_subsumed:                        1
% 2.36/1.00  sim_fw_subsumption_res:                 0
% 2.36/1.00  sim_bw_subsumption_res:                 0
% 2.36/1.00  sim_tautology_del:                      2
% 2.36/1.00  sim_eq_tautology_del:                   7
% 2.36/1.00  sim_eq_res_simp:                        2
% 2.36/1.00  sim_fw_demodulated:                     0
% 2.36/1.00  sim_bw_demodulated:                     28
% 2.36/1.00  sim_light_normalised:                   0
% 2.36/1.00  sim_joinable_taut:                      0
% 2.36/1.00  sim_joinable_simp:                      0
% 2.36/1.00  sim_ac_normalised:                      0
% 2.36/1.00  sim_smt_subsumption:                    0
% 2.36/1.00  
%------------------------------------------------------------------------------
