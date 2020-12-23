%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0734+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:00 EST 2020

% Result     : Theorem 1.22s
% Output     : CNFRefutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 213 expanded)
%              Number of clauses        :   61 (  73 expanded)
%              Number of leaves         :   18 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  373 ( 986 expanded)
%              Number of equality atoms :   68 (  83 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
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
    inference(nnf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,conjecture,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v1_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ! [X2] :
                ( v3_ordinal1(X2)
               => ( ( r2_hidden(X1,X2)
                    & r1_tarski(X0,X1) )
                 => r2_hidden(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X0,X2)
          & r2_hidden(X1,X2)
          & r1_tarski(X0,X1)
          & v3_ordinal1(X2) )
     => ( ~ r2_hidden(X0,sK4)
        & r2_hidden(X1,sK4)
        & r1_tarski(X0,X1)
        & v3_ordinal1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X0,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(X0,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
     => ( ? [X2] :
            ( ~ r2_hidden(X0,X2)
            & r2_hidden(sK3,X2)
            & r1_tarski(X0,sK3)
            & v3_ordinal1(X2) )
        & v3_ordinal1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X0,X2)
                & r2_hidden(X1,X2)
                & r1_tarski(X0,X1)
                & v3_ordinal1(X2) )
            & v3_ordinal1(X1) )
        & v1_ordinal1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(sK2,X2)
              & r2_hidden(X1,X2)
              & r1_tarski(sK2,X1)
              & v3_ordinal1(X2) )
          & v3_ordinal1(X1) )
      & v1_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ r2_hidden(sK2,sK4)
    & r2_hidden(sK3,sK4)
    & r1_tarski(sK2,sK3)
    & v3_ordinal1(sK4)
    & v3_ordinal1(sK3)
    & v1_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f31,f41,f40,f39])).

fof(f58,plain,(
    v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK0(X0),X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK0(X0),X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f44,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f57,plain,(
    v1_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1455,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3231,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2,sK4)
    | sK4 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1455])).

cnf(c_3233,plain,
    ( r2_hidden(sK2,sK4)
    | ~ r2_hidden(sK2,sK2)
    | sK4 != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3231])).

cnf(c_1454,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2246,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK2,sK4)
    | X1 != sK4
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_2911,plain,
    ( r1_tarski(sK4,X0)
    | ~ r1_tarski(sK2,sK4)
    | X0 != sK4
    | sK4 != sK2 ),
    inference(instantiation,[status(thm)],[c_2246])).

cnf(c_2913,plain,
    ( r1_tarski(sK4,sK2)
    | ~ r1_tarski(sK2,sK4)
    | sK4 != sK2
    | sK2 != sK4 ),
    inference(instantiation,[status(thm)],[c_2911])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2609,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2611,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ r1_tarski(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_2609])).

cnf(c_1452,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2447,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_1452])).

cnf(c_2448,plain,
    ( sK4 != sK2
    | sK2 = sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2447])).

cnf(c_2101,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK3,sK4)
    | X0 != sK3
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_1454])).

cnf(c_2331,plain,
    ( r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,sK4)
    | X0 != sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_2333,plain,
    ( ~ r1_tarski(sK3,sK4)
    | r1_tarski(sK3,sK2)
    | sK3 != sK3
    | sK2 != sK4 ),
    inference(instantiation,[status(thm)],[c_2331])).

cnf(c_1451,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2130,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_2122,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_1452])).

cnf(c_2123,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2122])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2047,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK2,X0)
    | ~ r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2115,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ r1_tarski(sK2,sK3)
    | r1_tarski(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_2047])).

cnf(c_2060,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3,sK4)
    | X0 != sK3
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_1455])).

cnf(c_2062,plain,
    ( ~ r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK2)
    | sK2 != sK3
    | sK2 != sK4 ),
    inference(instantiation,[status(thm)],[c_2060])).

cnf(c_1462,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_256,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_4,c_7])).

cnf(c_18,negated_conjecture,
    ( v3_ordinal1(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_314,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v1_ordinal1(X0)
    | X1 = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_256,c_18])).

cnf(c_315,plain,
    ( r2_hidden(X0,sK3)
    | ~ r1_tarski(X0,sK3)
    | ~ v1_ordinal1(X0)
    | sK3 = X0 ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_728,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X3,sK3)
    | ~ v1_ordinal1(X3)
    | X3 != X0
    | sK3 != X2
    | sK3 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_315])).

cnf(c_729,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,sK3)
    | ~ v1_ordinal1(X0)
    | sK3 = X0 ),
    inference(unflattening,[status(thm)],[c_728])).

cnf(c_731,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | m1_subset_1(sK2,sK2)
    | ~ r1_tarski(sK2,sK3)
    | ~ v1_ordinal1(sK2)
    | sK3 = sK2 ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_658,plain,
    ( r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_659,plain,
    ( r1_tarski(sK3,sK4)
    | ~ v1_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_147,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_148,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_147])).

cnf(c_185,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_148])).

cnf(c_646,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | sK3 != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_185,c_15])).

cnf(c_647,plain,
    ( ~ r1_tarski(sK4,X0)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_646])).

cnf(c_649,plain,
    ( ~ r1_tarski(sK4,sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_17,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_296,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v1_ordinal1(X0)
    | X1 = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_256,c_17])).

cnf(c_297,plain,
    ( r2_hidden(X0,sK4)
    | ~ r1_tarski(X0,sK4)
    | ~ v1_ordinal1(X0)
    | sK4 = X0 ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_19,negated_conjecture,
    ( v1_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_458,plain,
    ( r2_hidden(X0,sK4)
    | ~ r1_tarski(X0,sK4)
    | sK4 = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_297,c_19])).

cnf(c_459,plain,
    ( r2_hidden(sK2,sK4)
    | ~ r1_tarski(sK2,sK4)
    | sK4 = sK2 ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_0,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_282,plain,
    ( v1_ordinal1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_283,plain,
    ( v1_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_42,plain,
    ( ~ m1_subset_1(sK2,sK2)
    | r2_hidden(sK2,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3233,c_2913,c_2611,c_2448,c_2333,c_2130,c_2123,c_2115,c_2062,c_1462,c_731,c_659,c_649,c_459,c_283,c_42,c_14,c_15,c_16,c_19])).


%------------------------------------------------------------------------------
