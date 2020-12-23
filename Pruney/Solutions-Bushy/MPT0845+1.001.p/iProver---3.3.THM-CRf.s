%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0845+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:15 EST 2020

% Result     : Theorem 0.95s
% Output     : CNFRefutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :   58 (  74 expanded)
%              Number of clauses        :   25 (  25 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  156 ( 222 expanded)
%              Number of equality atoms :   19 (  27 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f18])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK1(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK1(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK1(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK1(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f20])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK1(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,conjecture,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ~ ( ! [X1] :
              ~ ( r1_xboole_0(X1,X0)
                & r2_hidden(X1,X0) )
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f17,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ r1_xboole_0(X1,X0)
          | ~ r2_hidden(X1,X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ r1_xboole_0(X1,X0)
            | ~ r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 )
   => ( ! [X1] :
          ( ~ r1_xboole_0(X1,sK2)
          | ~ r2_hidden(X1,sK2) )
      & k1_xboole_0 != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,sK2)
        | ~ r2_hidden(X1,sK2) )
    & k1_xboole_0 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f22])).

fof(f35,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK2)
      | ~ r2_hidden(X1,sK2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(o_1_0_mcart_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : m1_subset_1(o_1_0_mcart_1(X0),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f31,f24])).

fof(f34,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    o_0_0_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f34,f24])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1406,plain,
    ( r2_hidden(sK0(sK1(X0),X0),X0)
    | r1_xboole_0(sK1(X0),X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1408,plain,
    ( r2_hidden(sK0(sK1(sK2),sK2),sK2)
    | r1_xboole_0(sK1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_804,plain,
    ( r2_hidden(sK0(sK1(X0),X0),sK1(X0))
    | r1_xboole_0(sK1(X0),X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_810,plain,
    ( r2_hidden(sK0(sK1(sK2),sK2),sK1(sK2))
    | r1_xboole_0(sK1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,sK1(X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_444,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,sK1(X1))
    | ~ r2_hidden(o_1_0_mcart_1(X1),X1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_553,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),sK1(X1))
    | ~ r2_hidden(o_1_0_mcart_1(X1),X1) ),
    inference(instantiation,[status(thm)],[c_444])).

cnf(c_803,plain,
    ( ~ r2_hidden(sK0(sK1(X0),X0),X0)
    | ~ r2_hidden(sK0(sK1(X0),X0),sK1(X0))
    | ~ r2_hidden(o_1_0_mcart_1(X0),X0) ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_806,plain,
    ( ~ r2_hidden(sK0(sK1(sK2),sK2),sK1(sK2))
    | ~ r2_hidden(sK0(sK1(sK2),sK2),sK2)
    | ~ r2_hidden(o_1_0_mcart_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_9,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r1_xboole_0(X0,sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_482,plain,
    ( ~ r2_hidden(sK1(sK2),sK2)
    | ~ r1_xboole_0(sK1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK1(X1),X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_434,plain,
    ( r2_hidden(sK1(X0),X0)
    | ~ r2_hidden(o_1_0_mcart_1(X0),X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_436,plain,
    ( r2_hidden(sK1(sK2),sK2)
    | ~ r2_hidden(o_1_0_mcart_1(sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_0,plain,
    ( m1_subset_1(o_1_0_mcart_1(X0),X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_117,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | X1 != X2
    | o_1_0_mcart_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_118,plain,
    ( r2_hidden(o_1_0_mcart_1(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_117])).

cnf(c_120,plain,
    ( r2_hidden(o_1_0_mcart_1(sK2),sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_118])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_21,plain,
    ( ~ v1_xboole_0(sK2)
    | o_0_0_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_10,negated_conjecture,
    ( o_0_0_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1408,c_810,c_806,c_482,c_436,c_120,c_21,c_10])).


%------------------------------------------------------------------------------
