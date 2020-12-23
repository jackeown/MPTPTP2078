%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0742+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:02 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 265 expanded)
%              Number of clauses        :   79 (  97 expanded)
%              Number of leaves         :   17 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  460 (1243 expanded)
%              Number of equality atoms :   51 ( 127 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK0(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK0(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK0(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK0(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f39])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK0(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => r1_ordinal1(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ~ ( ! [X2] :
              ( v3_ordinal1(X2)
             => ~ ( ! [X3] :
                      ( v3_ordinal1(X3)
                     => ( r2_hidden(X3,X0)
                       => r1_ordinal1(X2,X3) ) )
                  & r2_hidden(X2,X0) ) )
          & k1_xboole_0 != X0
          & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ~ ( ! [X2] :
                ( v3_ordinal1(X2)
               => ~ ( ! [X3] :
                        ( v3_ordinal1(X3)
                       => ( r2_hidden(X3,X0)
                         => r1_ordinal1(X2,X3) ) )
                    & r2_hidden(X2,X0) ) )
            & k1_xboole_0 != X0
            & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f42,plain,(
    ! [X0,X2] :
      ( ? [X3] :
          ( ~ r1_ordinal1(X2,X3)
          & r2_hidden(X3,X0)
          & v3_ordinal1(X3) )
     => ( ~ r1_ordinal1(X2,sK3(X2))
        & r2_hidden(sK3(X2),X0)
        & v3_ordinal1(sK3(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( ~ r1_ordinal1(X2,X3)
                & r2_hidden(X3,X0)
                & v3_ordinal1(X3) )
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1)
        & v3_ordinal1(X1) )
   => ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,sK1)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,sK1)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != sK1
      & r1_tarski(sK1,sK2)
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ! [X2] :
        ( ( ~ r1_ordinal1(X2,sK3(X2))
          & r2_hidden(sK3(X2),sK1)
          & v3_ordinal1(sK3(X2)) )
        | ~ r2_hidden(X2,sK1)
        | ~ v3_ordinal1(X2) )
    & k1_xboole_0 != sK1
    & r1_tarski(sK1,sK2)
    & v3_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f36,f42,f41])).

fof(f65,plain,(
    ! [X2] :
      ( ~ r1_ordinal1(X2,sK3(X2))
      | ~ r2_hidden(X2,sK1)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    ! [X2] :
      ( v3_ordinal1(sK3(X2))
      | ~ r2_hidden(X2,sK1)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    ! [X2] :
      ( r2_hidden(sK3(X2),sK1)
      | ~ r2_hidden(X2,sK1)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(o_1_0_ordinal1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(o_1_0_ordinal1(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_0,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_284,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_285,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_7292,plain,
    ( ~ r2_hidden(X0,sK3(sK0(X1)))
    | r1_tarski(X0,sK3(sK0(X1)))
    | ~ v3_ordinal1(sK3(sK0(X1))) ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_14206,plain,
    ( ~ r2_hidden(sK0(X0),sK3(sK0(X1)))
    | r1_tarski(sK0(X0),sK3(sK0(X1)))
    | ~ v3_ordinal1(sK3(sK0(X1))) ),
    inference(instantiation,[status(thm)],[c_7292])).

cnf(c_14209,plain,
    ( ~ r2_hidden(sK0(sK1),sK3(sK0(sK1)))
    | r1_tarski(sK0(sK1),sK3(sK0(sK1)))
    | ~ v3_ordinal1(sK3(sK0(sK1))) ),
    inference(instantiation,[status(thm)],[c_14206])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2374,plain,
    ( r2_hidden(X0,sK0(X1))
    | r2_hidden(sK0(X1),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK0(X1))
    | X0 = sK0(X1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_13727,plain,
    ( r2_hidden(sK3(sK0(X0)),sK0(X1))
    | r2_hidden(sK0(X1),sK3(sK0(X0)))
    | ~ v3_ordinal1(sK3(sK0(X0)))
    | ~ v3_ordinal1(sK0(X1))
    | sK3(sK0(X0)) = sK0(X1) ),
    inference(instantiation,[status(thm)],[c_2374])).

cnf(c_13733,plain,
    ( r2_hidden(sK3(sK0(sK1)),sK0(sK1))
    | r2_hidden(sK0(sK1),sK3(sK0(sK1)))
    | ~ v3_ordinal1(sK3(sK0(sK1)))
    | ~ v3_ordinal1(sK0(sK1))
    | sK3(sK0(sK1)) = sK0(sK1) ),
    inference(instantiation,[status(thm)],[c_13727])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,sK0(X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1817,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK0(X1))
    | ~ r2_hidden(o_1_0_ordinal1(X1),X1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_7305,plain,
    ( ~ r2_hidden(sK3(sK0(X0)),sK0(sK1))
    | ~ r2_hidden(sK3(sK0(X0)),sK1)
    | ~ r2_hidden(o_1_0_ordinal1(sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_7320,plain,
    ( ~ r2_hidden(sK3(sK0(sK1)),sK0(sK1))
    | ~ r2_hidden(sK3(sK0(sK1)),sK1)
    | ~ r2_hidden(o_1_0_ordinal1(sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_7305])).

cnf(c_5,plain,
    ( r1_ordinal1(X0,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,negated_conjecture,
    ( ~ r1_ordinal1(X0,sK3(X0))
    | ~ r2_hidden(X0,sK1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_378,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X0)
    | X0 != X1
    | sK3(X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_16])).

cnf(c_379,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK3(X0) != X0 ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_948,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ v3_ordinal1(X0)
    | sK3(X0) != X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_379])).

cnf(c_949,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_379])).

cnf(c_947,plain,
    ( ~ v3_ordinal1(X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_379])).

cnf(c_1023,plain,
    ( sK3(X0) != X0
    | ~ v3_ordinal1(X0)
    | ~ r2_hidden(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_948,c_949,c_947])).

cnf(c_1024,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ v3_ordinal1(X0)
    | sK3(X0) != X0 ),
    inference(renaming,[status(thm)],[c_1023])).

cnf(c_4811,plain,
    ( ~ r2_hidden(sK0(X0),sK1)
    | ~ v3_ordinal1(sK0(X0))
    | sK3(sK0(X0)) != sK0(X0) ),
    inference(instantiation,[status(thm)],[c_1024])).

cnf(c_4826,plain,
    ( ~ r2_hidden(sK0(sK1),sK1)
    | ~ v3_ordinal1(sK0(sK1))
    | sK3(sK0(sK1)) != sK0(sK1) ),
    inference(instantiation,[status(thm)],[c_4811])).

cnf(c_3,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_357,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ r1_tarski(X1,X2)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X2)
    | ~ v3_ordinal1(X0)
    | X0 != X1
    | sK3(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_358,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ r1_tarski(X0,sK3(X0))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK3(X0)) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | ~ v3_ordinal1(X0)
    | v3_ordinal1(sK3(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_362,plain,
    ( ~ v3_ordinal1(X0)
    | ~ r1_tarski(X0,sK3(X0))
    | ~ r2_hidden(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_358,c_18])).

cnf(c_363,plain,
    ( ~ r2_hidden(X0,sK1)
    | ~ r1_tarski(X0,sK3(X0))
    | ~ v3_ordinal1(X0) ),
    inference(renaming,[status(thm)],[c_362])).

cnf(c_4812,plain,
    ( ~ r2_hidden(sK0(X0),sK1)
    | ~ r1_tarski(sK0(X0),sK3(sK0(X0)))
    | ~ v3_ordinal1(sK0(X0)) ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_4822,plain,
    ( ~ r2_hidden(sK0(sK1),sK1)
    | ~ r1_tarski(sK0(sK1),sK3(sK0(sK1)))
    | ~ v3_ordinal1(sK0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4812])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(X0,sK1)
    | r2_hidden(sK3(X0),sK1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4814,plain,
    ( r2_hidden(sK3(sK0(X0)),sK1)
    | ~ r2_hidden(sK0(X0),sK1)
    | ~ v3_ordinal1(sK0(X0)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4816,plain,
    ( r2_hidden(sK3(sK0(sK1)),sK1)
    | ~ r2_hidden(sK0(sK1),sK1)
    | ~ v3_ordinal1(sK0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4814])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1632,plain,
    ( ~ r2_hidden(X0,sK2)
    | v3_ordinal1(X0)
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4396,plain,
    ( ~ r2_hidden(sK0(X0),sK2)
    | v3_ordinal1(sK0(X0))
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_4402,plain,
    ( ~ r2_hidden(sK0(sK1),sK2)
    | v3_ordinal1(sK0(sK1))
    | ~ v3_ordinal1(sK2) ),
    inference(instantiation,[status(thm)],[c_4396])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_170,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_171,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_170])).

cnf(c_210,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_171])).

cnf(c_2108,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_210])).

cnf(c_3453,plain,
    ( ~ r2_hidden(o_1_0_ordinal1(X0),X0)
    | ~ r1_tarski(X0,sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_3455,plain,
    ( ~ r2_hidden(o_1_0_ordinal1(sK1),sK1)
    | ~ r1_tarski(sK1,sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3453])).

cnf(c_2,plain,
    ( m1_subset_1(o_1_0_ordinal1(X0),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1454,plain,
    ( m1_subset_1(o_1_0_ordinal1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1451,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2311,plain,
    ( r2_hidden(o_1_0_ordinal1(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1454,c_1451])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(X1),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1445,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK0(X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3229,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2311,c_1445])).

cnf(c_1443,plain,
    ( r2_hidden(X0,sK1) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK3(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3304,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v3_ordinal1(sK3(sK0(sK1))) = iProver_top
    | v3_ordinal1(sK0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3229,c_1443])).

cnf(c_3338,plain,
    ( v1_xboole_0(sK1)
    | v3_ordinal1(sK3(sK0(sK1)))
    | ~ v3_ordinal1(sK0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3304])).

cnf(c_2797,plain,
    ( ~ m1_subset_1(sK0(X0),sK2)
    | r2_hidden(sK0(X0),sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2799,plain,
    ( ~ m1_subset_1(sK0(sK1),sK2)
    | r2_hidden(sK0(sK1),sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2797])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1973,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X0),X1)
    | ~ r2_hidden(sK0(X0),X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2331,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | m1_subset_1(sK0(X0),sK2)
    | ~ r2_hidden(sK0(X0),X0) ),
    inference(instantiation,[status(thm)],[c_1973])).

cnf(c_2333,plain,
    ( m1_subset_1(sK0(sK1),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ r2_hidden(sK0(sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_2331])).

cnf(c_1818,plain,
    ( r2_hidden(sK0(X0),X0)
    | ~ r2_hidden(o_1_0_ordinal1(X0),X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1820,plain,
    ( r2_hidden(sK0(sK1),sK1)
    | ~ r2_hidden(o_1_0_ordinal1(sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_1818])).

cnf(c_1664,plain,
    ( ~ m1_subset_1(o_1_0_ordinal1(X0),X0)
    | r2_hidden(o_1_0_ordinal1(X0),X0)
    | v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1666,plain,
    ( ~ m1_subset_1(o_1_0_ordinal1(sK1),sK1)
    | r2_hidden(o_1_0_ordinal1(sK1),sK1)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1664])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_424,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_171,c_20])).

cnf(c_425,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_71,plain,
    ( m1_subset_1(o_1_0_ordinal1(sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_40,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_21,negated_conjecture,
    ( v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14209,c_13733,c_7320,c_4826,c_4822,c_4816,c_4402,c_3455,c_3338,c_2799,c_2333,c_1820,c_1666,c_425,c_71,c_40,c_19,c_20,c_21])).


%------------------------------------------------------------------------------
