%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0538+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:31 EST 2020

% Result     : Theorem 0.55s
% Output     : CNFRefutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :   10
%              Number of atoms          :  143 ( 146 expanded)
%              Number of equality atoms :   24 (  24 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK1(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
                    & r2_hidden(sK1(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f19])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,conjecture,(
    ! [X0] : k8_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k8_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0] : k8_relat_1(X0,k1_xboole_0) != k1_xboole_0 ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,
    ( ? [X0] : k8_relat_1(X0,k1_xboole_0) != k1_xboole_0
   => k8_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    k8_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f23])).

fof(f36,plain,(
    k8_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_8,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_138,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_10])).

cnf(c_139,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_138])).

cnf(c_219,plain,
    ( ~ r2_hidden(X0_39,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_139])).

cnf(c_548,plain,
    ( ~ r2_hidden(k4_tarski(sK0(X0_40,X1_40,k1_xboole_0),sK1(X0_40,X1_40,k1_xboole_0)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_219])).

cnf(c_650,plain,
    ( ~ r2_hidden(k4_tarski(sK0(sK4,k1_xboole_0,k1_xboole_0),sK1(sK4,k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_2,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X1)
    | r2_hidden(k4_tarski(sK0(X0,X1,X2),sK1(X0,X1,X2)),X2)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | k8_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_228,plain,
    ( r2_hidden(k4_tarski(sK0(X0_40,X1_40,X2_40),sK1(X0_40,X1_40,X2_40)),X2_40)
    | r2_hidden(k4_tarski(sK0(X0_40,X1_40,X2_40),sK1(X0_40,X1_40,X2_40)),X1_40)
    | ~ v1_relat_1(X1_40)
    | ~ v1_relat_1(X2_40)
    | k8_relat_1(X0_40,X1_40) = X2_40 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_608,plain,
    ( r2_hidden(k4_tarski(sK0(sK4,k1_xboole_0,k1_xboole_0),sK1(sK4,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k8_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_11,negated_conjecture,
    ( k8_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_221,negated_conjecture,
    ( k8_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_41,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_650,c_608,c_221,c_41,c_8])).


%------------------------------------------------------------------------------
