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
% DateTime   : Thu Dec  3 12:10:54 EST 2020

% Result     : CounterSatisfiable 2.27s
% Output     : Saturation 2.27s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 923 expanded)
%              Number of clauses        :   75 ( 234 expanded)
%              Number of leaves         :   23 ( 233 expanded)
%              Depth                    :   17
%              Number of atoms          :  348 (2191 expanded)
%              Number of equality atoms :  199 (1121 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | r1_tarski(sK0(X0,X1),X0)
      | r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f63])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f64])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f55,f48])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f39,f64])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f54,f65])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f18,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k2_struct_0(X0) = X1
                  & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                  & k2_struct_0(X0) != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f20,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ( ~ ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
          & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ( k2_struct_0(X0) = X1
          & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
        | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
          & k2_struct_0(X0) != X1 ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ( ( k2_struct_0(X0) = X1
            & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
          | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
            & k2_struct_0(X0) != X1 ) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
   => ( ( ( k2_struct_0(sK1) = sK2
          & k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) )
        | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)
          & k2_struct_0(sK1) != sK2 ) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ( ( k2_struct_0(sK1) = sK2
        & k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) )
      | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)
        & k2_struct_0(sK1) != sK2 ) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f34])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f65])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
      | ~ r1_tarski(sK0(X0,X1),X0)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f59,plain,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,
    ( k2_struct_0(sK1) = sK2
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_208,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_205,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_859,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_6,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(sK0(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_448,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_449,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_448])).

cnf(c_628,plain,
    ( r1_tarski(X0,X1)
    | r1_tarski(sK0(X2,X3),X2)
    | sK0(X2,X3) != X0
    | k1_zfmisc_1(X1) != X3
    | k1_zfmisc_1(X2) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_449])).

cnf(c_629,plain,
    ( r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X0)
    | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_1170,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X0) = iProver_top
    | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1177,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2122,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | k1_setfam_1(k2_enumset1(sK0(X1,k1_zfmisc_1(X0)),sK0(X1,k1_zfmisc_1(X0)),sK0(X1,k1_zfmisc_1(X0)),X0)) = sK0(X1,k1_zfmisc_1(X0))
    | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1177])).

cnf(c_2839,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1)) = sK0(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0)) = sK0(X0,k1_zfmisc_1(X1)) ),
    inference(superposition,[status(thm)],[c_2122,c_1177])).

cnf(c_11,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1175,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1188,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1175,c_9])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1173,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2229,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_1188,c_1173])).

cnf(c_3122,plain,
    ( k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1) = k5_xboole_0(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)))
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
    | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0)) = sK0(X0,k1_zfmisc_1(X1)) ),
    inference(superposition,[status(thm)],[c_2839,c_2229])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3128,plain,
    ( k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1) = k1_xboole_0
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
    | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0)) = sK0(X0,k1_zfmisc_1(X1)) ),
    inference(demodulation,[status(thm)],[c_3122,c_4])).

cnf(c_3142,plain,
    ( k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0) = k5_xboole_0(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)))
    | k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1) = k1_xboole_0
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X0) ),
    inference(superposition,[status(thm)],[c_3128,c_2229])).

cnf(c_3143,plain,
    ( k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1) = k1_xboole_0
    | k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0) = k1_xboole_0
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X0) ),
    inference(demodulation,[status(thm)],[c_3142,c_4])).

cnf(c_3121,plain,
    ( k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0) = k5_xboole_0(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)))
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
    | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1)) = sK0(X0,k1_zfmisc_1(X1)) ),
    inference(superposition,[status(thm)],[c_2839,c_2229])).

cnf(c_3135,plain,
    ( k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0) = k1_xboole_0
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
    | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1)) = sK0(X0,k1_zfmisc_1(X1)) ),
    inference(demodulation,[status(thm)],[c_3121,c_4])).

cnf(c_2125,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | k1_setfam_1(k2_enumset1(sK0(X1,k1_zfmisc_1(X0)),sK0(X1,k1_zfmisc_1(X0)),sK0(X1,k1_zfmisc_1(X0)),X1)) = sK0(X1,k1_zfmisc_1(X0))
    | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1177])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1179,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2863,plain,
    ( sK0(X0,k1_zfmisc_1(X1)) = X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0)) = sK0(X0,k1_zfmisc_1(X1))
    | r1_tarski(X1,sK0(X0,k1_zfmisc_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2125,c_1179])).

cnf(c_2838,plain,
    ( sK0(X0,k1_zfmisc_1(X1)) = X0
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1)) = sK0(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,sK0(X0,k1_zfmisc_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2122,c_1179])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1172,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2228,plain,
    ( k5_xboole_0(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,X0))) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
    inference(superposition,[status(thm)],[c_1172,c_1173])).

cnf(c_2466,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
    inference(demodulation,[status(thm)],[c_2228,c_2229])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1178,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1591,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1178,c_1177])).

cnf(c_2358,plain,
    ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1591,c_2229])).

cnf(c_2367,plain,
    ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2358,c_4])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_226,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_zfmisc_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_15])).

cnf(c_227,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_226])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_227,c_449])).

cnf(c_1171,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_2003,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1171])).

cnf(c_2109,plain,
    ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,u1_struct_0(sK1))) = sK2 ),
    inference(superposition,[status(thm)],[c_2003,c_1177])).

cnf(c_2359,plain,
    ( k7_subset_1(sK2,sK2,u1_struct_0(sK1)) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_2109,c_2229])).

cnf(c_2364,plain,
    ( k7_subset_1(sK2,sK2,u1_struct_0(sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2359,c_4])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1176,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1769,plain,
    ( k5_xboole_0(u1_struct_0(sK1),k1_setfam_1(k2_enumset1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK2))) = k3_subset_1(u1_struct_0(sK1),sK2) ),
    inference(superposition,[status(thm)],[c_1172,c_1176])).

cnf(c_2360,plain,
    ( k7_subset_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2) = k3_subset_1(u1_struct_0(sK1),sK2) ),
    inference(superposition,[status(thm)],[c_2229,c_1769])).

cnf(c_2353,plain,
    ( k7_subset_1(X0,X0,X1) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2229,c_1176])).

cnf(c_2231,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2229,c_1173])).

cnf(c_2124,plain,
    ( sK0(X0,k1_zfmisc_1(X1)) = X0
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
    | r1_tarski(X0,sK0(X0,k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1179])).

cnf(c_2121,plain,
    ( sK0(X0,k1_zfmisc_1(X1)) = X1
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
    | r1_tarski(X1,sK0(X0,k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1170,c_1179])).

cnf(c_2108,plain,
    ( u1_struct_0(sK1) = sK2
    | r1_tarski(u1_struct_0(sK1),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2003,c_1179])).

cnf(c_1770,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) = k3_subset_1(X0,X0) ),
    inference(superposition,[status(thm)],[c_1188,c_1176])).

cnf(c_1996,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1770,c_4,c_1591])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1174,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1581,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1172,c_1174])).

cnf(c_5,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r1_tarski(sK0(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_450,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_451,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_450])).

cnf(c_641,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK0(X2,X3),X2)
    | sK0(X2,X3) != X0
    | k1_zfmisc_1(X1) != X3
    | k1_zfmisc_1(X2) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_451])).

cnf(c_642,plain,
    ( ~ r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X0)
    | ~ r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_641])).

cnf(c_1169,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X0) != iProver_top
    | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_19,negated_conjecture,
    ( k2_struct_0(sK1) != sK2
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_16,negated_conjecture,
    ( k2_struct_0(sK1) = sK2
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f62])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:08:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.27/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/0.98  
% 2.27/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.27/0.98  
% 2.27/0.98  ------  iProver source info
% 2.27/0.98  
% 2.27/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.27/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.27/0.98  git: non_committed_changes: false
% 2.27/0.98  git: last_make_outside_of_git: false
% 2.27/0.98  
% 2.27/0.98  ------ 
% 2.27/0.98  
% 2.27/0.98  ------ Input Options
% 2.27/0.98  
% 2.27/0.98  --out_options                           all
% 2.27/0.98  --tptp_safe_out                         true
% 2.27/0.98  --problem_path                          ""
% 2.27/0.98  --include_path                          ""
% 2.27/0.98  --clausifier                            res/vclausify_rel
% 2.27/0.98  --clausifier_options                    --mode clausify
% 2.27/0.98  --stdin                                 false
% 2.27/0.98  --stats_out                             all
% 2.27/0.98  
% 2.27/0.98  ------ General Options
% 2.27/0.98  
% 2.27/0.98  --fof                                   false
% 2.27/0.98  --time_out_real                         305.
% 2.27/0.98  --time_out_virtual                      -1.
% 2.27/0.98  --symbol_type_check                     false
% 2.27/0.98  --clausify_out                          false
% 2.27/0.98  --sig_cnt_out                           false
% 2.27/0.98  --trig_cnt_out                          false
% 2.27/0.98  --trig_cnt_out_tolerance                1.
% 2.27/0.98  --trig_cnt_out_sk_spl                   false
% 2.27/0.98  --abstr_cl_out                          false
% 2.27/0.98  
% 2.27/0.98  ------ Global Options
% 2.27/0.98  
% 2.27/0.98  --schedule                              default
% 2.27/0.98  --add_important_lit                     false
% 2.27/0.98  --prop_solver_per_cl                    1000
% 2.27/0.98  --min_unsat_core                        false
% 2.27/0.98  --soft_assumptions                      false
% 2.27/0.98  --soft_lemma_size                       3
% 2.27/0.98  --prop_impl_unit_size                   0
% 2.27/0.98  --prop_impl_unit                        []
% 2.27/0.98  --share_sel_clauses                     true
% 2.27/0.98  --reset_solvers                         false
% 2.27/0.98  --bc_imp_inh                            [conj_cone]
% 2.27/0.98  --conj_cone_tolerance                   3.
% 2.27/0.98  --extra_neg_conj                        none
% 2.27/0.98  --large_theory_mode                     true
% 2.27/0.98  --prolific_symb_bound                   200
% 2.27/0.98  --lt_threshold                          2000
% 2.27/0.98  --clause_weak_htbl                      true
% 2.27/0.98  --gc_record_bc_elim                     false
% 2.27/0.98  
% 2.27/0.98  ------ Preprocessing Options
% 2.27/0.98  
% 2.27/0.98  --preprocessing_flag                    true
% 2.27/0.98  --time_out_prep_mult                    0.1
% 2.27/0.98  --splitting_mode                        input
% 2.27/0.98  --splitting_grd                         true
% 2.27/0.98  --splitting_cvd                         false
% 2.27/0.98  --splitting_cvd_svl                     false
% 2.27/0.98  --splitting_nvd                         32
% 2.27/0.98  --sub_typing                            true
% 2.27/0.98  --prep_gs_sim                           true
% 2.27/0.98  --prep_unflatten                        true
% 2.27/0.98  --prep_res_sim                          true
% 2.27/0.98  --prep_upred                            true
% 2.27/0.98  --prep_sem_filter                       exhaustive
% 2.27/0.98  --prep_sem_filter_out                   false
% 2.27/0.98  --pred_elim                             true
% 2.27/0.98  --res_sim_input                         true
% 2.27/0.98  --eq_ax_congr_red                       true
% 2.27/0.98  --pure_diseq_elim                       true
% 2.27/0.98  --brand_transform                       false
% 2.27/0.98  --non_eq_to_eq                          false
% 2.27/0.98  --prep_def_merge                        true
% 2.27/0.98  --prep_def_merge_prop_impl              false
% 2.27/0.98  --prep_def_merge_mbd                    true
% 2.27/0.98  --prep_def_merge_tr_red                 false
% 2.27/0.98  --prep_def_merge_tr_cl                  false
% 2.27/0.98  --smt_preprocessing                     true
% 2.27/0.98  --smt_ac_axioms                         fast
% 2.27/0.98  --preprocessed_out                      false
% 2.27/0.98  --preprocessed_stats                    false
% 2.27/0.98  
% 2.27/0.98  ------ Abstraction refinement Options
% 2.27/0.98  
% 2.27/0.98  --abstr_ref                             []
% 2.27/0.98  --abstr_ref_prep                        false
% 2.27/0.98  --abstr_ref_until_sat                   false
% 2.27/0.98  --abstr_ref_sig_restrict                funpre
% 2.27/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/0.98  --abstr_ref_under                       []
% 2.27/0.98  
% 2.27/0.98  ------ SAT Options
% 2.27/0.98  
% 2.27/0.98  --sat_mode                              false
% 2.27/0.98  --sat_fm_restart_options                ""
% 2.27/0.98  --sat_gr_def                            false
% 2.27/0.98  --sat_epr_types                         true
% 2.27/0.98  --sat_non_cyclic_types                  false
% 2.27/0.98  --sat_finite_models                     false
% 2.27/0.98  --sat_fm_lemmas                         false
% 2.27/0.98  --sat_fm_prep                           false
% 2.27/0.98  --sat_fm_uc_incr                        true
% 2.27/0.98  --sat_out_model                         small
% 2.27/0.98  --sat_out_clauses                       false
% 2.27/0.98  
% 2.27/0.98  ------ QBF Options
% 2.27/0.98  
% 2.27/0.98  --qbf_mode                              false
% 2.27/0.98  --qbf_elim_univ                         false
% 2.27/0.98  --qbf_dom_inst                          none
% 2.27/0.98  --qbf_dom_pre_inst                      false
% 2.27/0.98  --qbf_sk_in                             false
% 2.27/0.98  --qbf_pred_elim                         true
% 2.27/0.98  --qbf_split                             512
% 2.27/0.98  
% 2.27/0.98  ------ BMC1 Options
% 2.27/0.98  
% 2.27/0.98  --bmc1_incremental                      false
% 2.27/0.98  --bmc1_axioms                           reachable_all
% 2.27/0.98  --bmc1_min_bound                        0
% 2.27/0.98  --bmc1_max_bound                        -1
% 2.27/0.98  --bmc1_max_bound_default                -1
% 2.27/0.98  --bmc1_symbol_reachability              true
% 2.27/0.98  --bmc1_property_lemmas                  false
% 2.27/0.98  --bmc1_k_induction                      false
% 2.27/0.98  --bmc1_non_equiv_states                 false
% 2.27/0.98  --bmc1_deadlock                         false
% 2.27/0.98  --bmc1_ucm                              false
% 2.27/0.98  --bmc1_add_unsat_core                   none
% 2.27/0.98  --bmc1_unsat_core_children              false
% 2.27/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/0.98  --bmc1_out_stat                         full
% 2.27/0.98  --bmc1_ground_init                      false
% 2.27/0.98  --bmc1_pre_inst_next_state              false
% 2.27/0.98  --bmc1_pre_inst_state                   false
% 2.27/0.98  --bmc1_pre_inst_reach_state             false
% 2.27/0.98  --bmc1_out_unsat_core                   false
% 2.27/0.98  --bmc1_aig_witness_out                  false
% 2.27/0.98  --bmc1_verbose                          false
% 2.27/0.98  --bmc1_dump_clauses_tptp                false
% 2.27/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.27/0.98  --bmc1_dump_file                        -
% 2.27/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.27/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.27/0.98  --bmc1_ucm_extend_mode                  1
% 2.27/0.98  --bmc1_ucm_init_mode                    2
% 2.27/0.98  --bmc1_ucm_cone_mode                    none
% 2.27/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.27/0.98  --bmc1_ucm_relax_model                  4
% 2.27/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.27/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/0.98  --bmc1_ucm_layered_model                none
% 2.27/0.98  --bmc1_ucm_max_lemma_size               10
% 2.27/0.98  
% 2.27/0.98  ------ AIG Options
% 2.27/0.98  
% 2.27/0.98  --aig_mode                              false
% 2.27/0.98  
% 2.27/0.98  ------ Instantiation Options
% 2.27/0.98  
% 2.27/0.98  --instantiation_flag                    true
% 2.27/0.98  --inst_sos_flag                         false
% 2.27/0.98  --inst_sos_phase                        true
% 2.27/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/0.98  --inst_lit_sel_side                     num_symb
% 2.27/0.98  --inst_solver_per_active                1400
% 2.27/0.98  --inst_solver_calls_frac                1.
% 2.27/0.98  --inst_passive_queue_type               priority_queues
% 2.27/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/0.98  --inst_passive_queues_freq              [25;2]
% 2.27/0.98  --inst_dismatching                      true
% 2.27/0.98  --inst_eager_unprocessed_to_passive     true
% 2.27/0.98  --inst_prop_sim_given                   true
% 2.27/0.98  --inst_prop_sim_new                     false
% 2.27/0.98  --inst_subs_new                         false
% 2.27/0.98  --inst_eq_res_simp                      false
% 2.27/0.98  --inst_subs_given                       false
% 2.27/0.98  --inst_orphan_elimination               true
% 2.27/0.98  --inst_learning_loop_flag               true
% 2.27/0.98  --inst_learning_start                   3000
% 2.27/0.98  --inst_learning_factor                  2
% 2.27/0.98  --inst_start_prop_sim_after_learn       3
% 2.27/0.98  --inst_sel_renew                        solver
% 2.27/0.98  --inst_lit_activity_flag                true
% 2.27/0.98  --inst_restr_to_given                   false
% 2.27/0.98  --inst_activity_threshold               500
% 2.27/0.98  --inst_out_proof                        true
% 2.27/0.98  
% 2.27/0.98  ------ Resolution Options
% 2.27/0.98  
% 2.27/0.98  --resolution_flag                       true
% 2.27/0.98  --res_lit_sel                           adaptive
% 2.27/0.98  --res_lit_sel_side                      none
% 2.27/0.98  --res_ordering                          kbo
% 2.27/0.98  --res_to_prop_solver                    active
% 2.27/0.98  --res_prop_simpl_new                    false
% 2.27/0.98  --res_prop_simpl_given                  true
% 2.27/0.98  --res_passive_queue_type                priority_queues
% 2.27/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/0.98  --res_passive_queues_freq               [15;5]
% 2.27/0.98  --res_forward_subs                      full
% 2.27/0.98  --res_backward_subs                     full
% 2.27/0.98  --res_forward_subs_resolution           true
% 2.27/0.98  --res_backward_subs_resolution          true
% 2.27/0.98  --res_orphan_elimination                true
% 2.27/0.98  --res_time_limit                        2.
% 2.27/0.98  --res_out_proof                         true
% 2.27/0.98  
% 2.27/0.98  ------ Superposition Options
% 2.27/0.98  
% 2.27/0.98  --superposition_flag                    true
% 2.27/0.98  --sup_passive_queue_type                priority_queues
% 2.27/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.27/0.98  --demod_completeness_check              fast
% 2.27/0.98  --demod_use_ground                      true
% 2.27/0.98  --sup_to_prop_solver                    passive
% 2.27/0.98  --sup_prop_simpl_new                    true
% 2.27/0.98  --sup_prop_simpl_given                  true
% 2.27/0.98  --sup_fun_splitting                     false
% 2.27/0.98  --sup_smt_interval                      50000
% 2.27/0.98  
% 2.27/0.98  ------ Superposition Simplification Setup
% 2.27/0.98  
% 2.27/0.98  --sup_indices_passive                   []
% 2.27/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.98  --sup_full_bw                           [BwDemod]
% 2.27/0.98  --sup_immed_triv                        [TrivRules]
% 2.27/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.98  --sup_immed_bw_main                     []
% 2.27/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.98  
% 2.27/0.98  ------ Combination Options
% 2.27/0.98  
% 2.27/0.98  --comb_res_mult                         3
% 2.27/0.98  --comb_sup_mult                         2
% 2.27/0.98  --comb_inst_mult                        10
% 2.27/0.98  
% 2.27/0.98  ------ Debug Options
% 2.27/0.98  
% 2.27/0.98  --dbg_backtrace                         false
% 2.27/0.98  --dbg_dump_prop_clauses                 false
% 2.27/0.98  --dbg_dump_prop_clauses_file            -
% 2.27/0.98  --dbg_out_stat                          false
% 2.27/0.98  ------ Parsing...
% 2.27/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.27/0.98  
% 2.27/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.27/0.98  
% 2.27/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.27/0.98  
% 2.27/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.27/0.98  ------ Proving...
% 2.27/0.98  ------ Problem Properties 
% 2.27/0.98  
% 2.27/0.98  
% 2.27/0.98  clauses                                 15
% 2.27/0.98  conjectures                             3
% 2.27/0.98  EPR                                     2
% 2.27/0.98  Horn                                    13
% 2.27/0.98  unary                                   5
% 2.27/0.98  binary                                  7
% 2.27/0.98  lits                                    28
% 2.27/0.98  lits eq                                 13
% 2.27/0.98  fd_pure                                 0
% 2.27/0.98  fd_pseudo                               0
% 2.27/0.98  fd_cond                                 0
% 2.27/0.98  fd_pseudo_cond                          1
% 2.27/0.98  AC symbols                              0
% 2.27/0.98  
% 2.27/0.98  ------ Schedule dynamic 5 is on 
% 2.27/0.98  
% 2.27/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.27/0.98  
% 2.27/0.98  
% 2.27/0.98  ------ 
% 2.27/0.98  Current options:
% 2.27/0.98  ------ 
% 2.27/0.98  
% 2.27/0.98  ------ Input Options
% 2.27/0.98  
% 2.27/0.98  --out_options                           all
% 2.27/0.98  --tptp_safe_out                         true
% 2.27/0.98  --problem_path                          ""
% 2.27/0.98  --include_path                          ""
% 2.27/0.98  --clausifier                            res/vclausify_rel
% 2.27/0.98  --clausifier_options                    --mode clausify
% 2.27/0.98  --stdin                                 false
% 2.27/0.98  --stats_out                             all
% 2.27/0.98  
% 2.27/0.98  ------ General Options
% 2.27/0.98  
% 2.27/0.98  --fof                                   false
% 2.27/0.98  --time_out_real                         305.
% 2.27/0.98  --time_out_virtual                      -1.
% 2.27/0.98  --symbol_type_check                     false
% 2.27/0.98  --clausify_out                          false
% 2.27/0.98  --sig_cnt_out                           false
% 2.27/0.98  --trig_cnt_out                          false
% 2.27/0.98  --trig_cnt_out_tolerance                1.
% 2.27/0.98  --trig_cnt_out_sk_spl                   false
% 2.27/0.98  --abstr_cl_out                          false
% 2.27/0.98  
% 2.27/0.98  ------ Global Options
% 2.27/0.98  
% 2.27/0.98  --schedule                              default
% 2.27/0.98  --add_important_lit                     false
% 2.27/0.98  --prop_solver_per_cl                    1000
% 2.27/0.98  --min_unsat_core                        false
% 2.27/0.98  --soft_assumptions                      false
% 2.27/0.98  --soft_lemma_size                       3
% 2.27/0.98  --prop_impl_unit_size                   0
% 2.27/0.98  --prop_impl_unit                        []
% 2.27/0.98  --share_sel_clauses                     true
% 2.27/0.98  --reset_solvers                         false
% 2.27/0.98  --bc_imp_inh                            [conj_cone]
% 2.27/0.98  --conj_cone_tolerance                   3.
% 2.27/0.98  --extra_neg_conj                        none
% 2.27/0.98  --large_theory_mode                     true
% 2.27/0.98  --prolific_symb_bound                   200
% 2.27/0.98  --lt_threshold                          2000
% 2.27/0.98  --clause_weak_htbl                      true
% 2.27/0.98  --gc_record_bc_elim                     false
% 2.27/0.98  
% 2.27/0.98  ------ Preprocessing Options
% 2.27/0.98  
% 2.27/0.98  --preprocessing_flag                    true
% 2.27/0.98  --time_out_prep_mult                    0.1
% 2.27/0.98  --splitting_mode                        input
% 2.27/0.98  --splitting_grd                         true
% 2.27/0.98  --splitting_cvd                         false
% 2.27/0.98  --splitting_cvd_svl                     false
% 2.27/0.98  --splitting_nvd                         32
% 2.27/0.98  --sub_typing                            true
% 2.27/0.98  --prep_gs_sim                           true
% 2.27/0.98  --prep_unflatten                        true
% 2.27/0.98  --prep_res_sim                          true
% 2.27/0.98  --prep_upred                            true
% 2.27/0.98  --prep_sem_filter                       exhaustive
% 2.27/0.98  --prep_sem_filter_out                   false
% 2.27/0.98  --pred_elim                             true
% 2.27/0.98  --res_sim_input                         true
% 2.27/0.98  --eq_ax_congr_red                       true
% 2.27/0.98  --pure_diseq_elim                       true
% 2.27/0.98  --brand_transform                       false
% 2.27/0.98  --non_eq_to_eq                          false
% 2.27/0.98  --prep_def_merge                        true
% 2.27/0.98  --prep_def_merge_prop_impl              false
% 2.27/0.98  --prep_def_merge_mbd                    true
% 2.27/0.98  --prep_def_merge_tr_red                 false
% 2.27/0.98  --prep_def_merge_tr_cl                  false
% 2.27/0.98  --smt_preprocessing                     true
% 2.27/0.98  --smt_ac_axioms                         fast
% 2.27/0.98  --preprocessed_out                      false
% 2.27/0.98  --preprocessed_stats                    false
% 2.27/0.98  
% 2.27/0.98  ------ Abstraction refinement Options
% 2.27/0.98  
% 2.27/0.98  --abstr_ref                             []
% 2.27/0.98  --abstr_ref_prep                        false
% 2.27/0.98  --abstr_ref_until_sat                   false
% 2.27/0.98  --abstr_ref_sig_restrict                funpre
% 2.27/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.27/0.98  --abstr_ref_under                       []
% 2.27/0.98  
% 2.27/0.98  ------ SAT Options
% 2.27/0.98  
% 2.27/0.98  --sat_mode                              false
% 2.27/0.98  --sat_fm_restart_options                ""
% 2.27/0.98  --sat_gr_def                            false
% 2.27/0.98  --sat_epr_types                         true
% 2.27/0.98  --sat_non_cyclic_types                  false
% 2.27/0.98  --sat_finite_models                     false
% 2.27/0.98  --sat_fm_lemmas                         false
% 2.27/0.98  --sat_fm_prep                           false
% 2.27/0.98  --sat_fm_uc_incr                        true
% 2.27/0.98  --sat_out_model                         small
% 2.27/0.98  --sat_out_clauses                       false
% 2.27/0.98  
% 2.27/0.98  ------ QBF Options
% 2.27/0.98  
% 2.27/0.98  --qbf_mode                              false
% 2.27/0.98  --qbf_elim_univ                         false
% 2.27/0.98  --qbf_dom_inst                          none
% 2.27/0.98  --qbf_dom_pre_inst                      false
% 2.27/0.98  --qbf_sk_in                             false
% 2.27/0.98  --qbf_pred_elim                         true
% 2.27/0.98  --qbf_split                             512
% 2.27/0.98  
% 2.27/0.98  ------ BMC1 Options
% 2.27/0.98  
% 2.27/0.98  --bmc1_incremental                      false
% 2.27/0.98  --bmc1_axioms                           reachable_all
% 2.27/0.98  --bmc1_min_bound                        0
% 2.27/0.98  --bmc1_max_bound                        -1
% 2.27/0.98  --bmc1_max_bound_default                -1
% 2.27/0.98  --bmc1_symbol_reachability              true
% 2.27/0.98  --bmc1_property_lemmas                  false
% 2.27/0.98  --bmc1_k_induction                      false
% 2.27/0.98  --bmc1_non_equiv_states                 false
% 2.27/0.98  --bmc1_deadlock                         false
% 2.27/0.98  --bmc1_ucm                              false
% 2.27/0.98  --bmc1_add_unsat_core                   none
% 2.27/0.98  --bmc1_unsat_core_children              false
% 2.27/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.27/0.98  --bmc1_out_stat                         full
% 2.27/0.98  --bmc1_ground_init                      false
% 2.27/0.98  --bmc1_pre_inst_next_state              false
% 2.27/0.98  --bmc1_pre_inst_state                   false
% 2.27/0.98  --bmc1_pre_inst_reach_state             false
% 2.27/0.98  --bmc1_out_unsat_core                   false
% 2.27/0.98  --bmc1_aig_witness_out                  false
% 2.27/0.98  --bmc1_verbose                          false
% 2.27/0.98  --bmc1_dump_clauses_tptp                false
% 2.27/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.27/0.98  --bmc1_dump_file                        -
% 2.27/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.27/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.27/0.98  --bmc1_ucm_extend_mode                  1
% 2.27/0.98  --bmc1_ucm_init_mode                    2
% 2.27/0.98  --bmc1_ucm_cone_mode                    none
% 2.27/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.27/0.98  --bmc1_ucm_relax_model                  4
% 2.27/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.27/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.27/0.98  --bmc1_ucm_layered_model                none
% 2.27/0.98  --bmc1_ucm_max_lemma_size               10
% 2.27/0.98  
% 2.27/0.98  ------ AIG Options
% 2.27/0.98  
% 2.27/0.98  --aig_mode                              false
% 2.27/0.98  
% 2.27/0.98  ------ Instantiation Options
% 2.27/0.98  
% 2.27/0.98  --instantiation_flag                    true
% 2.27/0.98  --inst_sos_flag                         false
% 2.27/0.98  --inst_sos_phase                        true
% 2.27/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.27/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.27/0.98  --inst_lit_sel_side                     none
% 2.27/0.98  --inst_solver_per_active                1400
% 2.27/0.98  --inst_solver_calls_frac                1.
% 2.27/0.98  --inst_passive_queue_type               priority_queues
% 2.27/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.27/0.98  --inst_passive_queues_freq              [25;2]
% 2.27/0.98  --inst_dismatching                      true
% 2.27/0.98  --inst_eager_unprocessed_to_passive     true
% 2.27/0.98  --inst_prop_sim_given                   true
% 2.27/0.98  --inst_prop_sim_new                     false
% 2.27/0.98  --inst_subs_new                         false
% 2.27/0.98  --inst_eq_res_simp                      false
% 2.27/0.98  --inst_subs_given                       false
% 2.27/0.98  --inst_orphan_elimination               true
% 2.27/0.98  --inst_learning_loop_flag               true
% 2.27/0.98  --inst_learning_start                   3000
% 2.27/0.98  --inst_learning_factor                  2
% 2.27/0.98  --inst_start_prop_sim_after_learn       3
% 2.27/0.98  --inst_sel_renew                        solver
% 2.27/0.98  --inst_lit_activity_flag                true
% 2.27/0.98  --inst_restr_to_given                   false
% 2.27/0.98  --inst_activity_threshold               500
% 2.27/0.98  --inst_out_proof                        true
% 2.27/0.98  
% 2.27/0.98  ------ Resolution Options
% 2.27/0.98  
% 2.27/0.98  --resolution_flag                       false
% 2.27/0.98  --res_lit_sel                           adaptive
% 2.27/0.98  --res_lit_sel_side                      none
% 2.27/0.98  --res_ordering                          kbo
% 2.27/0.98  --res_to_prop_solver                    active
% 2.27/0.98  --res_prop_simpl_new                    false
% 2.27/0.98  --res_prop_simpl_given                  true
% 2.27/0.98  --res_passive_queue_type                priority_queues
% 2.27/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.27/0.98  --res_passive_queues_freq               [15;5]
% 2.27/0.98  --res_forward_subs                      full
% 2.27/0.98  --res_backward_subs                     full
% 2.27/0.98  --res_forward_subs_resolution           true
% 2.27/0.98  --res_backward_subs_resolution          true
% 2.27/0.98  --res_orphan_elimination                true
% 2.27/0.98  --res_time_limit                        2.
% 2.27/0.98  --res_out_proof                         true
% 2.27/0.98  
% 2.27/0.98  ------ Superposition Options
% 2.27/0.98  
% 2.27/0.98  --superposition_flag                    true
% 2.27/0.98  --sup_passive_queue_type                priority_queues
% 2.27/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.27/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.27/0.98  --demod_completeness_check              fast
% 2.27/0.98  --demod_use_ground                      true
% 2.27/0.98  --sup_to_prop_solver                    passive
% 2.27/0.98  --sup_prop_simpl_new                    true
% 2.27/0.98  --sup_prop_simpl_given                  true
% 2.27/0.98  --sup_fun_splitting                     false
% 2.27/0.98  --sup_smt_interval                      50000
% 2.27/0.98  
% 2.27/0.98  ------ Superposition Simplification Setup
% 2.27/0.98  
% 2.27/0.98  --sup_indices_passive                   []
% 2.27/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.27/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.27/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.98  --sup_full_bw                           [BwDemod]
% 2.27/0.98  --sup_immed_triv                        [TrivRules]
% 2.27/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.27/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.98  --sup_immed_bw_main                     []
% 2.27/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.27/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.27/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.27/0.98  
% 2.27/0.98  ------ Combination Options
% 2.27/0.98  
% 2.27/0.98  --comb_res_mult                         3
% 2.27/0.98  --comb_sup_mult                         2
% 2.27/0.98  --comb_inst_mult                        10
% 2.27/0.98  
% 2.27/0.98  ------ Debug Options
% 2.27/0.98  
% 2.27/0.98  --dbg_backtrace                         false
% 2.27/0.98  --dbg_dump_prop_clauses                 false
% 2.27/0.98  --dbg_dump_prop_clauses_file            -
% 2.27/0.98  --dbg_out_stat                          false
% 2.27/0.98  
% 2.27/0.98  
% 2.27/0.98  
% 2.27/0.98  
% 2.27/0.98  ------ Proving...
% 2.27/0.98  
% 2.27/0.98  
% 2.27/0.98  % SZS status CounterSatisfiable for theBenchmark.p
% 2.27/0.98  
% 2.27/0.98  % SZS output start Saturation for theBenchmark.p
% 2.27/0.98  
% 2.27/0.98  fof(f7,axiom,(
% 2.27/0.98    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.27/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.98  
% 2.27/0.98  fof(f30,plain,(
% 2.27/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.27/0.98    inference(nnf_transformation,[],[f7])).
% 2.27/0.98  
% 2.27/0.98  fof(f31,plain,(
% 2.27/0.98    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.27/0.98    inference(rectify,[],[f30])).
% 2.27/0.98  
% 2.27/0.98  fof(f32,plain,(
% 2.27/0.98    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 2.27/0.98    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f33,plain,(
% 2.27/0.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 2.27/0.99  
% 2.27/0.99  fof(f46,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k1_zfmisc_1(X0) = X1 | r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f33])).
% 2.27/0.99  
% 2.27/0.99  fof(f44,plain,(
% 2.27/0.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.27/0.99    inference(cnf_transformation,[],[f33])).
% 2.27/0.99  
% 2.27/0.99  fof(f75,plain,(
% 2.27/0.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.27/0.99    inference(equality_resolution,[],[f44])).
% 2.27/0.99  
% 2.27/0.99  fof(f3,axiom,(
% 2.27/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f21,plain,(
% 2.27/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.27/0.99    inference(ennf_transformation,[],[f3])).
% 2.27/0.99  
% 2.27/0.99  fof(f40,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f21])).
% 2.27/0.99  
% 2.27/0.99  fof(f16,axiom,(
% 2.27/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f56,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f16])).
% 2.27/0.99  
% 2.27/0.99  fof(f5,axiom,(
% 2.27/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f42,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f5])).
% 2.27/0.99  
% 2.27/0.99  fof(f6,axiom,(
% 2.27/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f43,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f6])).
% 2.27/0.99  
% 2.27/0.99  fof(f63,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.27/0.99    inference(definition_unfolding,[],[f42,f43])).
% 2.27/0.99  
% 2.27/0.99  fof(f64,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.27/0.99    inference(definition_unfolding,[],[f56,f63])).
% 2.27/0.99  
% 2.27/0.99  fof(f67,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.27/0.99    inference(definition_unfolding,[],[f40,f64])).
% 2.27/0.99  
% 2.27/0.99  fof(f11,axiom,(
% 2.27/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f51,plain,(
% 2.27/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f11])).
% 2.27/0.99  
% 2.27/0.99  fof(f15,axiom,(
% 2.27/0.99    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f55,plain,(
% 2.27/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f15])).
% 2.27/0.99  
% 2.27/0.99  fof(f8,axiom,(
% 2.27/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f48,plain,(
% 2.27/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f8])).
% 2.27/0.99  
% 2.27/0.99  fof(f66,plain,(
% 2.27/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.27/0.99    inference(definition_unfolding,[],[f55,f48])).
% 2.27/0.99  
% 2.27/0.99  fof(f70,plain,(
% 2.27/0.99    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 2.27/0.99    inference(definition_unfolding,[],[f51,f66])).
% 2.27/0.99  
% 2.27/0.99  fof(f9,axiom,(
% 2.27/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f49,plain,(
% 2.27/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.27/0.99    inference(cnf_transformation,[],[f9])).
% 2.27/0.99  
% 2.27/0.99  fof(f68,plain,(
% 2.27/0.99    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 2.27/0.99    inference(definition_unfolding,[],[f49,f66])).
% 2.27/0.99  
% 2.27/0.99  fof(f14,axiom,(
% 2.27/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f24,plain,(
% 2.27/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.27/0.99    inference(ennf_transformation,[],[f14])).
% 2.27/0.99  
% 2.27/0.99  fof(f54,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f24])).
% 2.27/0.99  
% 2.27/0.99  fof(f2,axiom,(
% 2.27/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f39,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f2])).
% 2.27/0.99  
% 2.27/0.99  fof(f65,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.27/0.99    inference(definition_unfolding,[],[f39,f64])).
% 2.27/0.99  
% 2.27/0.99  fof(f71,plain,(
% 2.27/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.27/0.99    inference(definition_unfolding,[],[f54,f65])).
% 2.27/0.99  
% 2.27/0.99  fof(f4,axiom,(
% 2.27/0.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f41,plain,(
% 2.27/0.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 2.27/0.99    inference(cnf_transformation,[],[f4])).
% 2.27/0.99  
% 2.27/0.99  fof(f1,axiom,(
% 2.27/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f28,plain,(
% 2.27/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.27/0.99    inference(nnf_transformation,[],[f1])).
% 2.27/0.99  
% 2.27/0.99  fof(f29,plain,(
% 2.27/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.27/0.99    inference(flattening,[],[f28])).
% 2.27/0.99  
% 2.27/0.99  fof(f38,plain,(
% 2.27/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f29])).
% 2.27/0.99  
% 2.27/0.99  fof(f18,conjecture,(
% 2.27/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f19,negated_conjecture,(
% 2.27/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 2.27/0.99    inference(negated_conjecture,[],[f18])).
% 2.27/0.99  
% 2.27/0.99  fof(f20,plain,(
% 2.27/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)))),
% 2.27/0.99    inference(pure_predicate_removal,[],[f19])).
% 2.27/0.99  
% 2.27/0.99  fof(f27,plain,(
% 2.27/0.99    ? [X0,X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 2.27/0.99    inference(ennf_transformation,[],[f20])).
% 2.27/0.99  
% 2.27/0.99  fof(f34,plain,(
% 2.27/0.99    ? [X0,X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((k2_struct_0(sK1) = sK2 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) & k2_struct_0(sK1) != sK2)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))),
% 2.27/0.99    introduced(choice_axiom,[])).
% 2.27/0.99  
% 2.27/0.99  fof(f35,plain,(
% 2.27/0.99    ((k2_struct_0(sK1) = sK2 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) & k2_struct_0(sK1) != sK2)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.27/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f34])).
% 2.27/0.99  
% 2.27/0.99  fof(f58,plain,(
% 2.27/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.27/0.99    inference(cnf_transformation,[],[f35])).
% 2.27/0.99  
% 2.27/0.99  fof(f37,plain,(
% 2.27/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.27/0.99    inference(cnf_transformation,[],[f29])).
% 2.27/0.99  
% 2.27/0.99  fof(f72,plain,(
% 2.27/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.27/0.99    inference(equality_resolution,[],[f37])).
% 2.27/0.99  
% 2.27/0.99  fof(f12,axiom,(
% 2.27/0.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f52,plain,(
% 2.27/0.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f12])).
% 2.27/0.99  
% 2.27/0.99  fof(f17,axiom,(
% 2.27/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f25,plain,(
% 2.27/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.27/0.99    inference(ennf_transformation,[],[f17])).
% 2.27/0.99  
% 2.27/0.99  fof(f26,plain,(
% 2.27/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.27/0.99    inference(flattening,[],[f25])).
% 2.27/0.99  
% 2.27/0.99  fof(f57,plain,(
% 2.27/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f26])).
% 2.27/0.99  
% 2.27/0.99  fof(f10,axiom,(
% 2.27/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f22,plain,(
% 2.27/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.27/0.99    inference(ennf_transformation,[],[f10])).
% 2.27/0.99  
% 2.27/0.99  fof(f50,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f22])).
% 2.27/0.99  
% 2.27/0.99  fof(f69,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.27/0.99    inference(definition_unfolding,[],[f50,f65])).
% 2.27/0.99  
% 2.27/0.99  fof(f13,axiom,(
% 2.27/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.27/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.27/0.99  
% 2.27/0.99  fof(f23,plain,(
% 2.27/0.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.27/0.99    inference(ennf_transformation,[],[f13])).
% 2.27/0.99  
% 2.27/0.99  fof(f53,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.27/0.99    inference(cnf_transformation,[],[f23])).
% 2.27/0.99  
% 2.27/0.99  fof(f47,plain,(
% 2.27/0.99    ( ! [X0,X1] : (k1_zfmisc_1(X0) = X1 | ~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.27/0.99    inference(cnf_transformation,[],[f33])).
% 2.27/0.99  
% 2.27/0.99  fof(f45,plain,(
% 2.27/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 2.27/0.99    inference(cnf_transformation,[],[f33])).
% 2.27/0.99  
% 2.27/0.99  fof(f74,plain,(
% 2.27/0.99    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 2.27/0.99    inference(equality_resolution,[],[f45])).
% 2.27/0.99  
% 2.27/0.99  fof(f59,plain,(
% 2.27/0.99    k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != sK2),
% 2.27/0.99    inference(cnf_transformation,[],[f35])).
% 2.27/0.99  
% 2.27/0.99  fof(f62,plain,(
% 2.27/0.99    k2_struct_0(sK1) = sK2 | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2)),
% 2.27/0.99    inference(cnf_transformation,[],[f35])).
% 2.27/0.99  
% 2.27/0.99  cnf(c_208,plain,
% 2.27/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.27/0.99      theory(equality) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_205,plain,
% 2.27/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.27/0.99      theory(equality) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_859,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_6,plain,
% 2.27/0.99      ( r2_hidden(sK0(X0,X1),X1)
% 2.27/0.99      | r1_tarski(sK0(X0,X1),X0)
% 2.27/0.99      | k1_zfmisc_1(X0) = X1 ),
% 2.27/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_8,plain,
% 2.27/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.27/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_448,plain,
% 2.27/0.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.27/0.99      inference(prop_impl,[status(thm)],[c_8]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_449,plain,
% 2.27/0.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.27/0.99      inference(renaming,[status(thm)],[c_448]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_628,plain,
% 2.27/0.99      ( r1_tarski(X0,X1)
% 2.27/0.99      | r1_tarski(sK0(X2,X3),X2)
% 2.27/0.99      | sK0(X2,X3) != X0
% 2.27/0.99      | k1_zfmisc_1(X1) != X3
% 2.27/0.99      | k1_zfmisc_1(X2) = X3 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_449]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_629,plain,
% 2.27/0.99      ( r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X0)
% 2.27/0.99      | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1)
% 2.27/0.99      | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_628]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1170,plain,
% 2.27/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.27/0.99      | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X0) = iProver_top
% 2.27/0.99      | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3,plain,
% 2.27/0.99      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ),
% 2.27/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1177,plain,
% 2.27/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
% 2.27/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2122,plain,
% 2.27/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.27/0.99      | k1_setfam_1(k2_enumset1(sK0(X1,k1_zfmisc_1(X0)),sK0(X1,k1_zfmisc_1(X0)),sK0(X1,k1_zfmisc_1(X0)),X0)) = sK0(X1,k1_zfmisc_1(X0))
% 2.27/0.99      | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X1) = iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1170,c_1177]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2839,plain,
% 2.27/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.27/0.99      | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1)) = sK0(X0,k1_zfmisc_1(X1))
% 2.27/0.99      | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0)) = sK0(X0,k1_zfmisc_1(X1)) ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2122,c_1177]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_11,plain,
% 2.27/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 2.27/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1175,plain,
% 2.27/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_9,plain,
% 2.27/0.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 2.27/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1188,plain,
% 2.27/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.27/0.99      inference(light_normalisation,[status(thm)],[c_1175,c_9]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_14,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.27/0.99      | k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 2.27/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1173,plain,
% 2.27/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
% 2.27/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2229,plain,
% 2.27/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1188,c_1173]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3122,plain,
% 2.27/0.99      ( k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1) = k5_xboole_0(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)))
% 2.27/0.99      | k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
% 2.27/0.99      | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0)) = sK0(X0,k1_zfmisc_1(X1)) ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2839,c_2229]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_4,plain,
% 2.27/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.27/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3128,plain,
% 2.27/0.99      ( k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
% 2.27/0.99      | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0)) = sK0(X0,k1_zfmisc_1(X1)) ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_3122,c_4]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3142,plain,
% 2.27/0.99      ( k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0) = k5_xboole_0(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)))
% 2.27/0.99      | k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(X1) = k1_zfmisc_1(X0) ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_3128,c_2229]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3143,plain,
% 2.27/0.99      ( k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1) = k1_xboole_0
% 2.27/0.99      | k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(X1) = k1_zfmisc_1(X0) ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_3142,c_4]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3121,plain,
% 2.27/0.99      ( k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0) = k5_xboole_0(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)))
% 2.27/0.99      | k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
% 2.27/0.99      | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1)) = sK0(X0,k1_zfmisc_1(X1)) ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2839,c_2229]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_3135,plain,
% 2.27/0.99      ( k7_subset_1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0) = k1_xboole_0
% 2.27/0.99      | k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
% 2.27/0.99      | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1)) = sK0(X0,k1_zfmisc_1(X1)) ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_3121,c_4]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2125,plain,
% 2.27/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.27/0.99      | k1_setfam_1(k2_enumset1(sK0(X1,k1_zfmisc_1(X0)),sK0(X1,k1_zfmisc_1(X0)),sK0(X1,k1_zfmisc_1(X0)),X1)) = sK0(X1,k1_zfmisc_1(X0))
% 2.27/0.99      | r1_tarski(sK0(X1,k1_zfmisc_1(X0)),X0) = iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1170,c_1177]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_0,plain,
% 2.27/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.27/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1179,plain,
% 2.27/0.99      ( X0 = X1
% 2.27/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.27/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2863,plain,
% 2.27/0.99      ( sK0(X0,k1_zfmisc_1(X1)) = X1
% 2.27/0.99      | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.27/0.99      | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X0)) = sK0(X0,k1_zfmisc_1(X1))
% 2.27/0.99      | r1_tarski(X1,sK0(X0,k1_zfmisc_1(X1))) != iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2125,c_1179]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2838,plain,
% 2.27/0.99      ( sK0(X0,k1_zfmisc_1(X1)) = X0
% 2.27/0.99      | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.27/0.99      | k1_setfam_1(k2_enumset1(sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),sK0(X0,k1_zfmisc_1(X1)),X1)) = sK0(X0,k1_zfmisc_1(X1))
% 2.27/0.99      | r1_tarski(X0,sK0(X0,k1_zfmisc_1(X1))) != iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2122,c_1179]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_20,negated_conjecture,
% 2.27/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.27/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1172,plain,
% 2.27/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2228,plain,
% 2.27/0.99      ( k5_xboole_0(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,X0))) = k7_subset_1(u1_struct_0(sK1),sK2,X0) ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1172,c_1173]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2466,plain,
% 2.27/0.99      ( k7_subset_1(u1_struct_0(sK1),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_2228,c_2229]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f72]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1178,plain,
% 2.27/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1591,plain,
% 2.27/0.99      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1178,c_1177]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2358,plain,
% 2.27/0.99      ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1591,c_2229]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2367,plain,
% 2.27/0.99      ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
% 2.27/0.99      inference(light_normalisation,[status(thm)],[c_2358,c_4]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_12,plain,
% 2.27/0.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.27/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_15,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.27/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_226,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_zfmisc_1(X2) != X1 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_15]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_227,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_226]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_485,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.27/0.99      inference(bin_hyper_res,[status(thm)],[c_227,c_449]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1171,plain,
% 2.27/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.27/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2003,plain,
% 2.27/0.99      ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1172,c_1171]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2109,plain,
% 2.27/0.99      ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,u1_struct_0(sK1))) = sK2 ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2003,c_1177]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2359,plain,
% 2.27/0.99      ( k7_subset_1(sK2,sK2,u1_struct_0(sK1)) = k5_xboole_0(sK2,sK2) ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2109,c_2229]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2364,plain,
% 2.27/0.99      ( k7_subset_1(sK2,sK2,u1_struct_0(sK1)) = k1_xboole_0 ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_2359,c_4]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_10,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.27/0.99      | k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
% 2.27/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1176,plain,
% 2.27/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k3_subset_1(X0,X1)
% 2.27/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1769,plain,
% 2.27/0.99      ( k5_xboole_0(u1_struct_0(sK1),k1_setfam_1(k2_enumset1(u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK1),sK2))) = k3_subset_1(u1_struct_0(sK1),sK2) ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1172,c_1176]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2360,plain,
% 2.27/0.99      ( k7_subset_1(u1_struct_0(sK1),u1_struct_0(sK1),sK2) = k3_subset_1(u1_struct_0(sK1),sK2) ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2229,c_1769]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2353,plain,
% 2.27/0.99      ( k7_subset_1(X0,X0,X1) = k3_subset_1(X0,X1)
% 2.27/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_2229,c_1176]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2231,plain,
% 2.27/0.99      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 2.27/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 2.27/0.99      inference(demodulation,[status(thm)],[c_2229,c_1173]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2124,plain,
% 2.27/0.99      ( sK0(X0,k1_zfmisc_1(X1)) = X0
% 2.27/0.99      | k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
% 2.27/0.99      | r1_tarski(X0,sK0(X0,k1_zfmisc_1(X1))) != iProver_top
% 2.27/0.99      | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) = iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1170,c_1179]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2121,plain,
% 2.27/0.99      ( sK0(X0,k1_zfmisc_1(X1)) = X1
% 2.27/0.99      | k1_zfmisc_1(X1) = k1_zfmisc_1(X0)
% 2.27/0.99      | r1_tarski(X1,sK0(X0,k1_zfmisc_1(X1))) != iProver_top
% 2.27/0.99      | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X0) = iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1170,c_1179]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_2108,plain,
% 2.27/0.99      ( u1_struct_0(sK1) = sK2
% 2.27/0.99      | r1_tarski(u1_struct_0(sK1),sK2) != iProver_top ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_2003,c_1179]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1770,plain,
% 2.27/0.99      ( k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X0))) = k3_subset_1(X0,X0) ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1188,c_1176]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1996,plain,
% 2.27/0.99      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 2.27/0.99      inference(light_normalisation,[status(thm)],[c_1770,c_4,c_1591]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_13,plain,
% 2.27/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.27/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 2.27/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1174,plain,
% 2.27/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 2.27/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1581,plain,
% 2.27/0.99      ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK2)) = sK2 ),
% 2.27/0.99      inference(superposition,[status(thm)],[c_1172,c_1174]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_5,plain,
% 2.27/0.99      ( ~ r2_hidden(sK0(X0,X1),X1)
% 2.27/0.99      | ~ r1_tarski(sK0(X0,X1),X0)
% 2.27/0.99      | k1_zfmisc_1(X0) = X1 ),
% 2.27/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_7,plain,
% 2.27/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.27/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_450,plain,
% 2.27/0.99      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 2.27/0.99      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_451,plain,
% 2.27/0.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.27/0.99      inference(renaming,[status(thm)],[c_450]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_641,plain,
% 2.27/0.99      ( ~ r1_tarski(X0,X1)
% 2.27/0.99      | ~ r1_tarski(sK0(X2,X3),X2)
% 2.27/0.99      | sK0(X2,X3) != X0
% 2.27/0.99      | k1_zfmisc_1(X1) != X3
% 2.27/0.99      | k1_zfmisc_1(X2) = X3 ),
% 2.27/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_451]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_642,plain,
% 2.27/0.99      ( ~ r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X0)
% 2.27/0.99      | ~ r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1)
% 2.27/0.99      | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.27/0.99      inference(unflattening,[status(thm)],[c_641]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_1169,plain,
% 2.27/0.99      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
% 2.27/0.99      | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X0) != iProver_top
% 2.27/0.99      | r1_tarski(sK0(X0,k1_zfmisc_1(X1)),X1) != iProver_top ),
% 2.27/0.99      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_19,negated_conjecture,
% 2.27/0.99      ( k2_struct_0(sK1) != sK2
% 2.27/0.99      | k1_xboole_0 != k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) ),
% 2.27/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.27/0.99  
% 2.27/0.99  cnf(c_16,negated_conjecture,
% 2.27/0.99      ( k2_struct_0(sK1) = sK2
% 2.27/0.99      | k1_xboole_0 = k7_subset_1(u1_struct_0(sK1),k2_struct_0(sK1),sK2) ),
% 2.27/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  % SZS output end Saturation for theBenchmark.p
% 2.27/0.99  
% 2.27/0.99  ------                               Statistics
% 2.27/0.99  
% 2.27/0.99  ------ General
% 2.27/0.99  
% 2.27/0.99  abstr_ref_over_cycles:                  0
% 2.27/0.99  abstr_ref_under_cycles:                 0
% 2.27/0.99  gc_basic_clause_elim:                   0
% 2.27/0.99  forced_gc_time:                         0
% 2.27/0.99  parsing_time:                           0.009
% 2.27/0.99  unif_index_cands_time:                  0.
% 2.27/0.99  unif_index_add_time:                    0.
% 2.27/0.99  orderings_time:                         0.
% 2.27/0.99  out_proof_time:                         0.
% 2.27/0.99  total_time:                             0.137
% 2.27/0.99  num_of_symbols:                         47
% 2.27/0.99  num_of_terms:                           2941
% 2.27/0.99  
% 2.27/0.99  ------ Preprocessing
% 2.27/0.99  
% 2.27/0.99  num_of_splits:                          0
% 2.27/0.99  num_of_split_atoms:                     0
% 2.27/0.99  num_of_reused_defs:                     0
% 2.27/0.99  num_eq_ax_congr_red:                    34
% 2.27/0.99  num_of_sem_filtered_clauses:            1
% 2.27/0.99  num_of_subtypes:                        0
% 2.27/0.99  monotx_restored_types:                  0
% 2.27/0.99  sat_num_of_epr_types:                   0
% 2.27/0.99  sat_num_of_non_cyclic_types:            0
% 2.27/0.99  sat_guarded_non_collapsed_types:        0
% 2.27/0.99  num_pure_diseq_elim:                    0
% 2.27/0.99  simp_replaced_by:                       0
% 2.27/0.99  res_preprocessed:                       105
% 2.27/0.99  prep_upred:                             0
% 2.27/0.99  prep_unflattend:                        35
% 2.27/0.99  smt_new_axioms:                         0
% 2.27/0.99  pred_elim_cands:                        2
% 2.27/0.99  pred_elim:                              2
% 2.27/0.99  pred_elim_cl:                           3
% 2.27/0.99  pred_elim_cycles:                       7
% 2.27/0.99  merged_defs:                            14
% 2.27/0.99  merged_defs_ncl:                        0
% 2.27/0.99  bin_hyper_res:                          15
% 2.27/0.99  prep_cycles:                            5
% 2.27/0.99  pred_elim_time:                         0.02
% 2.27/0.99  splitting_time:                         0.
% 2.27/0.99  sem_filter_time:                        0.
% 2.27/0.99  monotx_time:                            0.001
% 2.27/0.99  subtype_inf_time:                       0.
% 2.27/0.99  
% 2.27/0.99  ------ Problem properties
% 2.27/0.99  
% 2.27/0.99  clauses:                                15
% 2.27/0.99  conjectures:                            3
% 2.27/0.99  epr:                                    2
% 2.27/0.99  horn:                                   13
% 2.27/0.99  ground:                                 3
% 2.27/0.99  unary:                                  5
% 2.27/0.99  binary:                                 7
% 2.27/0.99  lits:                                   28
% 2.27/0.99  lits_eq:                                13
% 2.27/0.99  fd_pure:                                0
% 2.27/0.99  fd_pseudo:                              0
% 2.27/0.99  fd_cond:                                0
% 2.27/0.99  fd_pseudo_cond:                         1
% 2.27/0.99  ac_symbols:                             0
% 2.27/0.99  
% 2.27/0.99  ------ Propositional Solver
% 2.27/0.99  
% 2.27/0.99  prop_solver_calls:                      31
% 2.27/0.99  prop_fast_solver_calls:                 568
% 2.27/0.99  smt_solver_calls:                       0
% 2.27/0.99  smt_fast_solver_calls:                  0
% 2.27/0.99  prop_num_of_clauses:                    1052
% 2.27/0.99  prop_preprocess_simplified:             3841
% 2.27/0.99  prop_fo_subsumed:                       0
% 2.27/0.99  prop_solver_time:                       0.
% 2.27/0.99  smt_solver_time:                        0.
% 2.27/0.99  smt_fast_solver_time:                   0.
% 2.27/0.99  prop_fast_solver_time:                  0.
% 2.27/0.99  prop_unsat_core_time:                   0.
% 2.27/0.99  
% 2.27/0.99  ------ QBF
% 2.27/0.99  
% 2.27/0.99  qbf_q_res:                              0
% 2.27/0.99  qbf_num_tautologies:                    0
% 2.27/0.99  qbf_prep_cycles:                        0
% 2.27/0.99  
% 2.27/0.99  ------ BMC1
% 2.27/0.99  
% 2.27/0.99  bmc1_current_bound:                     -1
% 2.27/0.99  bmc1_last_solved_bound:                 -1
% 2.27/0.99  bmc1_unsat_core_size:                   -1
% 2.27/0.99  bmc1_unsat_core_parents_size:           -1
% 2.27/0.99  bmc1_merge_next_fun:                    0
% 2.27/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.27/0.99  
% 2.27/0.99  ------ Instantiation
% 2.27/0.99  
% 2.27/0.99  inst_num_of_clauses:                    341
% 2.27/0.99  inst_num_in_passive:                    63
% 2.27/0.99  inst_num_in_active:                     185
% 2.27/0.99  inst_num_in_unprocessed:                93
% 2.27/0.99  inst_num_of_loops:                      210
% 2.27/0.99  inst_num_of_learning_restarts:          0
% 2.27/0.99  inst_num_moves_active_passive:          22
% 2.27/0.99  inst_lit_activity:                      0
% 2.27/0.99  inst_lit_activity_moves:                0
% 2.27/0.99  inst_num_tautologies:                   0
% 2.27/0.99  inst_num_prop_implied:                  0
% 2.27/0.99  inst_num_existing_simplified:           0
% 2.27/0.99  inst_num_eq_res_simplified:             0
% 2.27/0.99  inst_num_child_elim:                    0
% 2.27/0.99  inst_num_of_dismatching_blockings:      193
% 2.27/0.99  inst_num_of_non_proper_insts:           447
% 2.27/0.99  inst_num_of_duplicates:                 0
% 2.27/0.99  inst_inst_num_from_inst_to_res:         0
% 2.27/0.99  inst_dismatching_checking_time:         0.
% 2.27/0.99  
% 2.27/0.99  ------ Resolution
% 2.27/0.99  
% 2.27/0.99  res_num_of_clauses:                     0
% 2.27/0.99  res_num_in_passive:                     0
% 2.27/0.99  res_num_in_active:                      0
% 2.27/0.99  res_num_of_loops:                       110
% 2.27/0.99  res_forward_subset_subsumed:            36
% 2.27/0.99  res_backward_subset_subsumed:           0
% 2.27/0.99  res_forward_subsumed:                   0
% 2.27/0.99  res_backward_subsumed:                  0
% 2.27/0.99  res_forward_subsumption_resolution:     0
% 2.27/0.99  res_backward_subsumption_resolution:    0
% 2.27/0.99  res_clause_to_clause_subsumption:       220
% 2.27/0.99  res_orphan_elimination:                 0
% 2.27/0.99  res_tautology_del:                      58
% 2.27/0.99  res_num_eq_res_simplified:              0
% 2.27/0.99  res_num_sel_changes:                    0
% 2.27/0.99  res_moves_from_active_to_pass:          0
% 2.27/0.99  
% 2.27/0.99  ------ Superposition
% 2.27/0.99  
% 2.27/0.99  sup_time_total:                         0.
% 2.27/0.99  sup_time_generating:                    0.
% 2.27/0.99  sup_time_sim_full:                      0.
% 2.27/0.99  sup_time_sim_immed:                     0.
% 2.27/0.99  
% 2.27/0.99  sup_num_of_clauses:                     40
% 2.27/0.99  sup_num_in_active:                      37
% 2.27/0.99  sup_num_in_passive:                     3
% 2.27/0.99  sup_num_of_loops:                       40
% 2.27/0.99  sup_fw_superposition:                   18
% 2.27/0.99  sup_bw_superposition:                   20
% 2.27/0.99  sup_immediate_simplified:               9
% 2.27/0.99  sup_given_eliminated:                   1
% 2.27/0.99  comparisons_done:                       0
% 2.27/0.99  comparisons_avoided:                    18
% 2.27/0.99  
% 2.27/0.99  ------ Simplifications
% 2.27/0.99  
% 2.27/0.99  
% 2.27/0.99  sim_fw_subset_subsumed:                 0
% 2.27/0.99  sim_bw_subset_subsumed:                 0
% 2.27/0.99  sim_fw_subsumed:                        2
% 2.27/0.99  sim_bw_subsumed:                        0
% 2.27/0.99  sim_fw_subsumption_res:                 0
% 2.27/0.99  sim_bw_subsumption_res:                 0
% 2.27/0.99  sim_tautology_del:                      3
% 2.27/0.99  sim_eq_tautology_del:                   7
% 2.27/0.99  sim_eq_res_simp:                        0
% 2.27/0.99  sim_fw_demodulated:                     6
% 2.27/0.99  sim_bw_demodulated:                     3
% 2.27/0.99  sim_light_normalised:                   4
% 2.27/0.99  sim_joinable_taut:                      0
% 2.27/0.99  sim_joinable_simp:                      0
% 2.27/0.99  sim_ac_normalised:                      0
% 2.27/0.99  sim_smt_subsumption:                    0
% 2.27/0.99  
%------------------------------------------------------------------------------
