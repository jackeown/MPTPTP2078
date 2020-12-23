%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:55 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.07s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 169 expanded)
%              Number of clauses        :   62 (  72 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  315 ( 580 expanded)
%              Number of equality atoms :   91 ( 130 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f20,plain,(
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

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f33])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
        | k1_xboole_0 != k7_relat_1(sK2,sK1) )
      & ( r1_xboole_0(k1_relat_1(sK2),sK1)
        | k1_xboole_0 = k7_relat_1(sK2,sK1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
      | k1_xboole_0 != k7_relat_1(sK2,sK1) )
    & ( r1_xboole_0(k1_relat_1(sK2),sK1)
      | k1_xboole_0 = k7_relat_1(sK2,sK1) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f39])).

fof(f66,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 != k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2604,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),X0)
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
    | ~ r1_xboole_0(k1_relat_1(sK2),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_18121,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
    | ~ r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_2604])).

cnf(c_6427,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),X0)
    | ~ r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ r1_xboole_0(k1_relat_1(sK2),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9523,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | ~ r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),sK1)
    | ~ r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_6427])).

cnf(c_441,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1199,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k1_relat_1(sK2),X2)
    | X2 != X1
    | k1_relat_1(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_3059,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1)))
    | k1_relat_1(k7_relat_1(sK2,sK1)) != X1
    | k1_relat_1(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1199])).

cnf(c_7161,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK2),X0)
    | r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1)))
    | k1_relat_1(k7_relat_1(sK2,sK1)) != X0
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3059])).

cnf(c_7163,plain,
    ( r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ r1_xboole_0(k1_relat_1(sK2),k1_xboole_0)
    | k1_relat_1(k7_relat_1(sK2,sK1)) != k1_xboole_0
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7161])).

cnf(c_16,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_6393,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
    | r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2571,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(X0))
    | r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(X0,sK1)))
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3384,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
    | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2571])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1179,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),X0),X0)
    | r1_xboole_0(k1_relat_1(sK2),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3050,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
    | r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_1179])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1178,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),X0),k1_relat_1(sK2))
    | r1_xboole_0(k1_relat_1(sK2),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3051,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2))
    | r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_1178])).

cnf(c_440,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_439,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1913,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_440,c_439])).

cnf(c_11,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2549,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1913,c_11])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X1,X2)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_17,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_254,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | ~ v1_relat_1(X3)
    | k1_relat_1(X3) != X0
    | k1_relat_1(k7_relat_1(X3,X4)) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_255,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X2)),X1)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_1101,plain,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X1)
    | ~ r1_xboole_0(k1_relat_1(sK2),X1)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_2355,plain,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1)))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1697,plain,
    ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(k7_relat_1(sK2,sK1)))
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1587,plain,
    ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_439])).

cnf(c_446,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_1502,plain,
    ( k7_relat_1(sK2,sK1) != X0
    | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_446])).

cnf(c_1504,plain,
    ( k7_relat_1(sK2,sK1) != k1_xboole_0
    | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1502])).

cnf(c_1339,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) != X0
    | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_1501,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(X0)
    | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1339])).

cnf(c_1503,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1501])).

cnf(c_1499,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) = k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_439])).

cnf(c_1498,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(k7_relat_1(sK2,sK1))
    | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k7_relat_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1339])).

cnf(c_19,negated_conjecture,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_894,plain,
    ( k1_xboole_0 = k7_relat_1(sK2,sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_909,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1286,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | r1_xboole_0(sK1,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_894,c_909])).

cnf(c_1414,plain,
    ( k7_relat_1(sK2,sK1) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1286,c_909])).

cnf(c_1415,plain,
    ( r1_xboole_0(k1_relat_1(sK2),sK1)
    | k7_relat_1(sK2,sK1) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1414])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1050,plain,
    ( v1_relat_1(k7_relat_1(sK2,X0))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1203,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1189,plain,
    ( r1_xboole_0(k1_relat_1(sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1132,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
    | k1_relat_1(k7_relat_1(sK2,sK1)) != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1079,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
    | r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1076,plain,
    ( r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
    | r1_xboole_0(k1_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_18,negated_conjecture,
    ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
    | k1_xboole_0 != k7_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18121,c_9523,c_7163,c_6393,c_3384,c_3050,c_3051,c_2549,c_2355,c_1697,c_1587,c_1504,c_1503,c_1499,c_1498,c_1415,c_1203,c_1189,c_1132,c_1079,c_1076,c_18,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:03:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.07/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.07/0.98  
% 4.07/0.98  ------  iProver source info
% 4.07/0.98  
% 4.07/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.07/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.07/0.98  git: non_committed_changes: false
% 4.07/0.98  git: last_make_outside_of_git: false
% 4.07/0.98  
% 4.07/0.98  ------ 
% 4.07/0.98  ------ Parsing...
% 4.07/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.07/0.98  
% 4.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.07/0.98  ------ Proving...
% 4.07/0.98  ------ Problem Properties 
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  clauses                                 20
% 4.07/0.98  conjectures                             3
% 4.07/0.98  EPR                                     6
% 4.07/0.98  Horn                                    17
% 4.07/0.98  unary                                   5
% 4.07/0.98  binary                                  8
% 4.07/0.98  lits                                    43
% 4.07/0.98  lits eq                                 9
% 4.07/0.98  fd_pure                                 0
% 4.07/0.98  fd_pseudo                               0
% 4.07/0.98  fd_cond                                 3
% 4.07/0.98  fd_pseudo_cond                          0
% 4.07/0.98  AC symbols                              0
% 4.07/0.98  
% 4.07/0.98  ------ Input Options Time Limit: Unbounded
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  ------ 
% 4.07/0.98  Current options:
% 4.07/0.98  ------ 
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  ------ Proving...
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  % SZS status Theorem for theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  fof(f2,axiom,(
% 4.07/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f20,plain,(
% 4.07/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 4.07/0.98    inference(rectify,[],[f2])).
% 4.07/0.98  
% 4.07/0.98  fof(f22,plain,(
% 4.07/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 4.07/0.98    inference(ennf_transformation,[],[f20])).
% 4.07/0.98  
% 4.07/0.98  fof(f33,plain,(
% 4.07/0.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 4.07/0.98    introduced(choice_axiom,[])).
% 4.07/0.98  
% 4.07/0.98  fof(f34,plain,(
% 4.07/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 4.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f33])).
% 4.07/0.98  
% 4.07/0.98  fof(f44,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f34])).
% 4.07/0.98  
% 4.07/0.98  fof(f16,axiom,(
% 4.07/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f30,plain,(
% 4.07/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 4.07/0.98    inference(ennf_transformation,[],[f16])).
% 4.07/0.98  
% 4.07/0.98  fof(f35,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 4.07/0.98    inference(nnf_transformation,[],[f30])).
% 4.07/0.98  
% 4.07/0.98  fof(f36,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 4.07/0.98    inference(flattening,[],[f35])).
% 4.07/0.98  
% 4.07/0.98  fof(f61,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~v1_relat_1(X2)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f36])).
% 4.07/0.98  
% 4.07/0.98  fof(f63,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f36])).
% 4.07/0.98  
% 4.07/0.98  fof(f43,plain,(
% 4.07/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f34])).
% 4.07/0.98  
% 4.07/0.98  fof(f42,plain,(
% 4.07/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f34])).
% 4.07/0.98  
% 4.07/0.98  fof(f14,axiom,(
% 4.07/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f57,plain,(
% 4.07/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.07/0.98    inference(cnf_transformation,[],[f14])).
% 4.07/0.98  
% 4.07/0.98  fof(f3,axiom,(
% 4.07/0.98    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f23,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 4.07/0.98    inference(ennf_transformation,[],[f3])).
% 4.07/0.98  
% 4.07/0.98  fof(f24,plain,(
% 4.07/0.98    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 4.07/0.98    inference(flattening,[],[f23])).
% 4.07/0.98  
% 4.07/0.98  fof(f45,plain,(
% 4.07/0.98    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f24])).
% 4.07/0.98  
% 4.07/0.98  fof(f17,axiom,(
% 4.07/0.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f31,plain,(
% 4.07/0.98    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 4.07/0.98    inference(ennf_transformation,[],[f17])).
% 4.07/0.98  
% 4.07/0.98  fof(f64,plain,(
% 4.07/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f31])).
% 4.07/0.98  
% 4.07/0.98  fof(f5,axiom,(
% 4.07/0.98    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f25,plain,(
% 4.07/0.98    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 4.07/0.98    inference(ennf_transformation,[],[f5])).
% 4.07/0.98  
% 4.07/0.98  fof(f48,plain,(
% 4.07/0.98    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 4.07/0.98    inference(cnf_transformation,[],[f25])).
% 4.07/0.98  
% 4.07/0.98  fof(f18,conjecture,(
% 4.07/0.98    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f19,negated_conjecture,(
% 4.07/0.98    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 4.07/0.98    inference(negated_conjecture,[],[f18])).
% 4.07/0.98  
% 4.07/0.98  fof(f32,plain,(
% 4.07/0.98    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 4.07/0.98    inference(ennf_transformation,[],[f19])).
% 4.07/0.98  
% 4.07/0.98  fof(f37,plain,(
% 4.07/0.98    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 4.07/0.98    inference(nnf_transformation,[],[f32])).
% 4.07/0.98  
% 4.07/0.98  fof(f38,plain,(
% 4.07/0.98    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 4.07/0.98    inference(flattening,[],[f37])).
% 4.07/0.98  
% 4.07/0.98  fof(f39,plain,(
% 4.07/0.98    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 != k7_relat_1(sK2,sK1)) & (r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 = k7_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 4.07/0.98    introduced(choice_axiom,[])).
% 4.07/0.98  
% 4.07/0.98  fof(f40,plain,(
% 4.07/0.98    (~r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 != k7_relat_1(sK2,sK1)) & (r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 = k7_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 4.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f38,f39])).
% 4.07/0.98  
% 4.07/0.98  fof(f66,plain,(
% 4.07/0.98    r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 = k7_relat_1(sK2,sK1)),
% 4.07/0.98    inference(cnf_transformation,[],[f40])).
% 4.07/0.98  
% 4.07/0.98  fof(f1,axiom,(
% 4.07/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f21,plain,(
% 4.07/0.98    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 4.07/0.98    inference(ennf_transformation,[],[f1])).
% 4.07/0.98  
% 4.07/0.98  fof(f41,plain,(
% 4.07/0.98    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f21])).
% 4.07/0.98  
% 4.07/0.98  fof(f13,axiom,(
% 4.07/0.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f27,plain,(
% 4.07/0.98    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 4.07/0.98    inference(ennf_transformation,[],[f13])).
% 4.07/0.98  
% 4.07/0.98  fof(f56,plain,(
% 4.07/0.98    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f27])).
% 4.07/0.98  
% 4.07/0.98  fof(f4,axiom,(
% 4.07/0.98    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f46,plain,(
% 4.07/0.98    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f4])).
% 4.07/0.98  
% 4.07/0.98  fof(f15,axiom,(
% 4.07/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 4.07/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.07/0.98  
% 4.07/0.98  fof(f28,plain,(
% 4.07/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.07/0.98    inference(ennf_transformation,[],[f15])).
% 4.07/0.98  
% 4.07/0.98  fof(f29,plain,(
% 4.07/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.07/0.98    inference(flattening,[],[f28])).
% 4.07/0.98  
% 4.07/0.98  fof(f59,plain,(
% 4.07/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.07/0.98    inference(cnf_transformation,[],[f29])).
% 4.07/0.98  
% 4.07/0.98  fof(f67,plain,(
% 4.07/0.98    ~r1_xboole_0(k1_relat_1(sK2),sK1) | k1_xboole_0 != k7_relat_1(sK2,sK1)),
% 4.07/0.98    inference(cnf_transformation,[],[f40])).
% 4.07/0.98  
% 4.07/0.98  fof(f65,plain,(
% 4.07/0.98    v1_relat_1(sK2)),
% 4.07/0.98    inference(cnf_transformation,[],[f40])).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1,plain,
% 4.07/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 4.07/0.98      inference(cnf_transformation,[],[f44]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_2604,plain,
% 4.07/0.98      ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),X0)
% 4.07/0.98      | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
% 4.07/0.98      | ~ r1_xboole_0(k1_relat_1(sK2),X0) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_18121,plain,
% 4.07/0.98      ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(sK2,sK1)))
% 4.07/0.98      | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
% 4.07/0.98      | ~ r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_2604]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_6427,plain,
% 4.07/0.98      ( ~ r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),X0)
% 4.07/0.98      | ~ r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2))
% 4.07/0.98      | ~ r1_xboole_0(k1_relat_1(sK2),X0) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_9523,plain,
% 4.07/0.98      ( ~ r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2))
% 4.07/0.98      | ~ r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),sK1)
% 4.07/0.98      | ~ r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_6427]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_441,plain,
% 4.07/0.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.07/0.98      theory(equality) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1199,plain,
% 4.07/0.98      ( ~ r1_xboole_0(X0,X1)
% 4.07/0.98      | r1_xboole_0(k1_relat_1(sK2),X2)
% 4.07/0.98      | X2 != X1
% 4.07/0.98      | k1_relat_1(sK2) != X0 ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_441]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_3059,plain,
% 4.07/0.98      ( ~ r1_xboole_0(X0,X1)
% 4.07/0.98      | r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1)))
% 4.07/0.98      | k1_relat_1(k7_relat_1(sK2,sK1)) != X1
% 4.07/0.98      | k1_relat_1(sK2) != X0 ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_1199]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_7161,plain,
% 4.07/0.98      ( ~ r1_xboole_0(k1_relat_1(sK2),X0)
% 4.07/0.98      | r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1)))
% 4.07/0.98      | k1_relat_1(k7_relat_1(sK2,sK1)) != X0
% 4.07/0.98      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_3059]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_7163,plain,
% 4.07/0.98      ( r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1)))
% 4.07/0.98      | ~ r1_xboole_0(k1_relat_1(sK2),k1_xboole_0)
% 4.07/0.98      | k1_relat_1(k7_relat_1(sK2,sK1)) != k1_xboole_0
% 4.07/0.98      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_7161]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_16,plain,
% 4.07/0.98      ( r2_hidden(X0,X1)
% 4.07/0.98      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 4.07/0.98      | ~ v1_relat_1(X2) ),
% 4.07/0.98      inference(cnf_transformation,[],[f61]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_6393,plain,
% 4.07/0.98      ( ~ r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
% 4.07/0.98      | r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),sK1)
% 4.07/0.98      | ~ v1_relat_1(sK2) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_14,plain,
% 4.07/0.98      ( ~ r2_hidden(X0,X1)
% 4.07/0.98      | ~ r2_hidden(X0,k1_relat_1(X2))
% 4.07/0.98      | r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
% 4.07/0.98      | ~ v1_relat_1(X2) ),
% 4.07/0.98      inference(cnf_transformation,[],[f63]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_2571,plain,
% 4.07/0.98      ( ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(X0))
% 4.07/0.98      | r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(X0,sK1)))
% 4.07/0.98      | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
% 4.07/0.98      | ~ v1_relat_1(X0) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_3384,plain,
% 4.07/0.98      ( r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(k7_relat_1(sK2,sK1)))
% 4.07/0.98      | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
% 4.07/0.98      | ~ r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
% 4.07/0.98      | ~ v1_relat_1(sK2) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_2571]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_2,plain,
% 4.07/0.98      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 4.07/0.98      inference(cnf_transformation,[],[f43]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1179,plain,
% 4.07/0.98      ( r2_hidden(sK0(k1_relat_1(sK2),X0),X0)
% 4.07/0.98      | r1_xboole_0(k1_relat_1(sK2),X0) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_3050,plain,
% 4.07/0.98      ( r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(k7_relat_1(sK2,sK1)))
% 4.07/0.98      | r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_1179]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_3,plain,
% 4.07/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 4.07/0.98      inference(cnf_transformation,[],[f42]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1178,plain,
% 4.07/0.98      ( r2_hidden(sK0(k1_relat_1(sK2),X0),k1_relat_1(sK2))
% 4.07/0.98      | r1_xboole_0(k1_relat_1(sK2),X0) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_3051,plain,
% 4.07/0.98      ( r2_hidden(sK0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))),k1_relat_1(sK2))
% 4.07/0.98      | r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1))) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_1178]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_440,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_439,plain,( X0 = X0 ),theory(equality) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1913,plain,
% 4.07/0.98      ( X0 != X1 | X1 = X0 ),
% 4.07/0.98      inference(resolution,[status(thm)],[c_440,c_439]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_11,plain,
% 4.07/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.07/0.98      inference(cnf_transformation,[],[f57]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_2549,plain,
% 4.07/0.98      ( k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 4.07/0.98      inference(resolution,[status(thm)],[c_1913,c_11]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_4,plain,
% 4.07/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) ),
% 4.07/0.98      inference(cnf_transformation,[],[f45]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_17,plain,
% 4.07/0.98      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 4.07/0.98      | ~ v1_relat_1(X0) ),
% 4.07/0.98      inference(cnf_transformation,[],[f64]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_254,plain,
% 4.07/0.98      ( ~ r1_xboole_0(X0,X1)
% 4.07/0.98      | r1_xboole_0(X2,X1)
% 4.07/0.98      | ~ v1_relat_1(X3)
% 4.07/0.98      | k1_relat_1(X3) != X0
% 4.07/0.98      | k1_relat_1(k7_relat_1(X3,X4)) != X2 ),
% 4.07/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_255,plain,
% 4.07/0.98      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 4.07/0.98      | r1_xboole_0(k1_relat_1(k7_relat_1(X0,X2)),X1)
% 4.07/0.98      | ~ v1_relat_1(X0) ),
% 4.07/0.98      inference(unflattening,[status(thm)],[c_254]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1101,plain,
% 4.07/0.98      ( r1_xboole_0(k1_relat_1(k7_relat_1(sK2,X0)),X1)
% 4.07/0.98      | ~ r1_xboole_0(k1_relat_1(sK2),X1)
% 4.07/0.98      | ~ v1_relat_1(sK2) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_255]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_2355,plain,
% 4.07/0.98      ( r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(k7_relat_1(sK2,sK1)))
% 4.07/0.98      | ~ r1_xboole_0(k1_relat_1(sK2),k1_relat_1(k7_relat_1(sK2,sK1)))
% 4.07/0.98      | ~ v1_relat_1(sK2) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_1101]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_6,plain,
% 4.07/0.98      ( ~ r1_xboole_0(X0,X0) | k1_xboole_0 = X0 ),
% 4.07/0.98      inference(cnf_transformation,[],[f48]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1697,plain,
% 4.07/0.98      ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK1)),k1_relat_1(k7_relat_1(sK2,sK1)))
% 4.07/0.98      | k1_xboole_0 = k1_relat_1(k7_relat_1(sK2,sK1)) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1587,plain,
% 4.07/0.98      ( k1_relat_1(sK2) = k1_relat_1(sK2) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_439]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_446,plain,
% 4.07/0.98      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 4.07/0.98      theory(equality) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1502,plain,
% 4.07/0.98      ( k7_relat_1(sK2,sK1) != X0
% 4.07/0.98      | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_relat_1(X0) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_446]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1504,plain,
% 4.07/0.98      ( k7_relat_1(sK2,sK1) != k1_xboole_0
% 4.07/0.98      | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_relat_1(k1_xboole_0) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_1502]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1339,plain,
% 4.07/0.98      ( k1_relat_1(k7_relat_1(sK2,sK1)) != X0
% 4.07/0.98      | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0
% 4.07/0.98      | k1_xboole_0 != X0 ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_440]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1501,plain,
% 4.07/0.98      ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(X0)
% 4.07/0.98      | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0
% 4.07/0.98      | k1_xboole_0 != k1_relat_1(X0) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_1339]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1503,plain,
% 4.07/0.98      ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(k1_xboole_0)
% 4.07/0.98      | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0
% 4.07/0.98      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_1501]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1499,plain,
% 4.07/0.98      ( k1_relat_1(k7_relat_1(sK2,sK1)) = k1_relat_1(k7_relat_1(sK2,sK1)) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_439]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1498,plain,
% 4.07/0.98      ( k1_relat_1(k7_relat_1(sK2,sK1)) != k1_relat_1(k7_relat_1(sK2,sK1))
% 4.07/0.98      | k1_relat_1(k7_relat_1(sK2,sK1)) = k1_xboole_0
% 4.07/0.98      | k1_xboole_0 != k1_relat_1(k7_relat_1(sK2,sK1)) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_1339]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_19,negated_conjecture,
% 4.07/0.98      ( r1_xboole_0(k1_relat_1(sK2),sK1)
% 4.07/0.98      | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
% 4.07/0.98      inference(cnf_transformation,[],[f66]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_894,plain,
% 4.07/0.98      ( k1_xboole_0 = k7_relat_1(sK2,sK1)
% 4.07/0.98      | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_0,plain,
% 4.07/0.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 4.07/0.98      inference(cnf_transformation,[],[f41]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_909,plain,
% 4.07/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 4.07/0.98      | r1_xboole_0(X1,X0) = iProver_top ),
% 4.07/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1286,plain,
% 4.07/0.98      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 4.07/0.98      | r1_xboole_0(sK1,k1_relat_1(sK2)) = iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_894,c_909]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1414,plain,
% 4.07/0.98      ( k7_relat_1(sK2,sK1) = k1_xboole_0
% 4.07/0.98      | r1_xboole_0(k1_relat_1(sK2),sK1) = iProver_top ),
% 4.07/0.98      inference(superposition,[status(thm)],[c_1286,c_909]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1415,plain,
% 4.07/0.98      ( r1_xboole_0(k1_relat_1(sK2),sK1)
% 4.07/0.98      | k7_relat_1(sK2,sK1) = k1_xboole_0 ),
% 4.07/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1414]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_9,plain,
% 4.07/0.98      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 4.07/0.98      inference(cnf_transformation,[],[f56]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1050,plain,
% 4.07/0.98      ( v1_relat_1(k7_relat_1(sK2,X0)) | ~ v1_relat_1(sK2) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1203,plain,
% 4.07/0.98      ( v1_relat_1(k7_relat_1(sK2,sK1)) | ~ v1_relat_1(sK2) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_1050]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_5,plain,
% 4.07/0.98      ( r1_xboole_0(X0,k1_xboole_0) ),
% 4.07/0.98      inference(cnf_transformation,[],[f46]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1189,plain,
% 4.07/0.98      ( r1_xboole_0(k1_relat_1(sK2),k1_xboole_0) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_13,plain,
% 4.07/0.98      ( ~ v1_relat_1(X0)
% 4.07/0.98      | k1_relat_1(X0) != k1_xboole_0
% 4.07/0.98      | k1_xboole_0 = X0 ),
% 4.07/0.98      inference(cnf_transformation,[],[f59]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1132,plain,
% 4.07/0.98      ( ~ v1_relat_1(k7_relat_1(sK2,sK1))
% 4.07/0.98      | k1_relat_1(k7_relat_1(sK2,sK1)) != k1_xboole_0
% 4.07/0.98      | k1_xboole_0 = k7_relat_1(sK2,sK1) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1079,plain,
% 4.07/0.98      ( r2_hidden(sK0(k1_relat_1(sK2),sK1),k1_relat_1(sK2))
% 4.07/0.98      | r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_1076,plain,
% 4.07/0.98      ( r2_hidden(sK0(k1_relat_1(sK2),sK1),sK1)
% 4.07/0.98      | r1_xboole_0(k1_relat_1(sK2),sK1) ),
% 4.07/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_18,negated_conjecture,
% 4.07/0.98      ( ~ r1_xboole_0(k1_relat_1(sK2),sK1)
% 4.07/0.98      | k1_xboole_0 != k7_relat_1(sK2,sK1) ),
% 4.07/0.98      inference(cnf_transformation,[],[f67]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(c_20,negated_conjecture,
% 4.07/0.98      ( v1_relat_1(sK2) ),
% 4.07/0.98      inference(cnf_transformation,[],[f65]) ).
% 4.07/0.98  
% 4.07/0.98  cnf(contradiction,plain,
% 4.07/0.98      ( $false ),
% 4.07/0.98      inference(minisat,
% 4.07/0.98                [status(thm)],
% 4.07/0.98                [c_18121,c_9523,c_7163,c_6393,c_3384,c_3050,c_3051,
% 4.07/0.98                 c_2549,c_2355,c_1697,c_1587,c_1504,c_1503,c_1499,c_1498,
% 4.07/0.98                 c_1415,c_1203,c_1189,c_1132,c_1079,c_1076,c_18,c_20]) ).
% 4.07/0.98  
% 4.07/0.98  
% 4.07/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.07/0.98  
% 4.07/0.98  ------                               Statistics
% 4.07/0.98  
% 4.07/0.98  ------ Selected
% 4.07/0.98  
% 4.07/0.98  total_time:                             0.495
% 4.07/0.98  
%------------------------------------------------------------------------------
