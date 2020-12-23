%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0610+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:43 EST 2020

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 156 expanded)
%              Number of clauses        :   41 (  48 expanded)
%              Number of leaves         :   13 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  226 ( 594 expanded)
%              Number of equality atoms :   68 (  84 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f11,f22])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ! [X1] :
      ( ? [X2,X3] : k4_tarski(X2,X3) = X1
     => k4_tarski(sK0(X1),sK1(X1)) = X1 ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tarski(sK0(X1),sK1(X1)) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_tarski(sK0(X1),sK1(X1)) = X1
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
           => r1_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
             => r1_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(X0,X1)
          & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          & v1_relat_1(X1) )
     => ( ~ r1_xboole_0(X0,sK7)
        & r1_xboole_0(k1_relat_1(X0),k1_relat_1(sK7))
        & v1_relat_1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(X0,X1)
            & r1_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(sK6,X1)
          & r1_xboole_0(k1_relat_1(sK6),k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ r1_xboole_0(sK6,sK7)
    & r1_xboole_0(k1_relat_1(sK6),k1_relat_1(sK7))
    & v1_relat_1(sK7)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f13,f25,f24])).

fof(f36,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f39,plain,(
    ~ r1_xboole_0(sK6,sK7) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
     => r2_hidden(k4_tarski(X2,sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f20,f19,f18])).

fof(f29,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X6),X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f38,plain,(
    r1_xboole_0(k1_relat_1(sK6),k1_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f26])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f26])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK5(X0,X1),X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_485,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK5(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(sK0(X0),sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_156,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(sK0(X0),sK1(X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_157,plain,
    ( ~ r2_hidden(X0,sK6)
    | k4_tarski(sK0(X0),sK1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_156])).

cnf(c_481,plain,
    ( k4_tarski(sK0(X0),sK1(X0)) = X0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_900,plain,
    ( k4_tarski(sK0(sK5(sK6,X0)),sK1(sK5(sK6,X0))) = sK5(sK6,X0)
    | r1_xboole_0(sK6,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_485,c_481])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(sK6,sK7) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_484,plain,
    ( r1_xboole_0(sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1766,plain,
    ( k4_tarski(sK0(sK5(sK6,sK7)),sK1(sK5(sK6,sK7))) = sK5(sK6,sK7) ),
    inference(superposition,[status(thm)],[c_900,c_484])).

cnf(c_3,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X0,X2),X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_490,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1873,plain,
    ( r2_hidden(sK5(sK6,sK7),X0) != iProver_top
    | r2_hidden(sK0(sK5(sK6,sK7)),k1_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1766,c_490])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK6),k1_relat_1(sK7)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_483,plain,
    ( r1_xboole_0(k1_relat_1(sK6),k1_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_487,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1019,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_483,c_487])).

cnf(c_1881,plain,
    ( r2_hidden(sK5(sK6,sK7),sK7) != iProver_top
    | r2_hidden(sK0(sK5(sK6,sK7)),k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1873,c_1019])).

cnf(c_1139,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK5(sK6,sK7)),sK1(sK5(sK6,sK7))),X0)
    | r2_hidden(sK0(sK5(sK6,sK7)),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1140,plain,
    ( r2_hidden(k4_tarski(sK0(sK5(sK6,sK7)),sK1(sK5(sK6,sK7))),X0) != iProver_top
    | r2_hidden(sK0(sK5(sK6,sK7)),k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1139])).

cnf(c_1142,plain,
    ( r2_hidden(k4_tarski(sK0(sK5(sK6,sK7)),sK1(sK5(sK6,sK7))),sK6) != iProver_top
    | r2_hidden(sK0(sK5(sK6,sK7)),k1_relat_1(sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_264,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_616,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5(sK6,sK7),sK6)
    | X0 != sK5(sK6,sK7)
    | X1 != sK6 ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_729,plain,
    ( ~ r2_hidden(sK5(sK6,sK7),sK6)
    | r2_hidden(k4_tarski(sK0(sK5(sK6,sK7)),sK1(sK5(sK6,sK7))),X0)
    | X0 != sK6
    | k4_tarski(sK0(sK5(sK6,sK7)),sK1(sK5(sK6,sK7))) != sK5(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_616])).

cnf(c_730,plain,
    ( X0 != sK6
    | k4_tarski(sK0(sK5(sK6,sK7)),sK1(sK5(sK6,sK7))) != sK5(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK5(sK6,sK7)),sK1(sK5(sK6,sK7))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_732,plain,
    ( k4_tarski(sK0(sK5(sK6,sK7)),sK1(sK5(sK6,sK7))) != sK5(sK6,sK7)
    | sK6 != sK6
    | r2_hidden(sK5(sK6,sK7),sK6) != iProver_top
    | r2_hidden(k4_tarski(sK0(sK5(sK6,sK7)),sK1(sK5(sK6,sK7))),sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_144,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(sK0(X0),sK1(X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_145,plain,
    ( ~ r2_hidden(X0,sK7)
    | k4_tarski(sK0(X0),sK1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_144])).

cnf(c_613,plain,
    ( ~ r2_hidden(sK5(sK6,sK7),sK7)
    | k4_tarski(sK0(sK5(sK6,sK7)),sK1(sK5(sK6,sK7))) = sK5(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_145])).

cnf(c_575,plain,
    ( r1_xboole_0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7),sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_576,plain,
    ( r1_xboole_0(sK6,sK7) = iProver_top
    | r2_hidden(sK5(sK6,sK7),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_575])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK5(X0,X1),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_572,plain,
    ( r1_xboole_0(sK6,sK7)
    | r2_hidden(sK5(sK6,sK7),sK7) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_573,plain,
    ( r1_xboole_0(sK6,sK7) = iProver_top
    | r2_hidden(sK5(sK6,sK7),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_572])).

cnf(c_261,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_272,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_261])).

cnf(c_16,plain,
    ( r1_xboole_0(sK6,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1881,c_1142,c_732,c_613,c_576,c_573,c_572,c_272,c_16,c_9])).


%------------------------------------------------------------------------------
