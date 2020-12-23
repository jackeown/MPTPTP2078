%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0776+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:06 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 133 expanded)
%              Number of clauses        :   38 (  44 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  277 ( 594 expanded)
%              Number of equality atoms :   66 ( 113 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | ~ r2_hidden(k4_tarski(X2,X1),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f18,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | ~ r2_hidden(k4_tarski(X2,X1),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & r2_hidden(k4_tarski(X2,X1),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & r2_hidden(k4_tarski(X2,X1),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( sK1(X0) != sK2(X0)
        & r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
        & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ( sK1(X0) != sK2(X0)
            & r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
            & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | ~ r2_hidden(k4_tarski(X4,X3),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0) )
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f19,f20])).

fof(f32,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | sK1(X0) != sK2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
       => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v4_relat_2(X1)
         => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ v4_relat_2(k2_wellord1(X1,X0))
      & v4_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ~ v4_relat_2(k2_wellord1(X1,X0))
      & v4_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ~ v4_relat_2(k2_wellord1(X1,X0))
        & v4_relat_2(X1)
        & v1_relat_1(X1) )
   => ( ~ v4_relat_2(k2_wellord1(sK4,sK3))
      & v4_relat_2(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ v4_relat_2(k2_wellord1(sK4,sK3))
    & v4_relat_2(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f12,f22])).

fof(f38,plain,(
    ~ v4_relat_2(k2_wellord1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    v4_relat_2(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_7339,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)))
    | r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_309,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_761,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | X0 != k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3)))
    | X1 != k2_wellord1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_873,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | X0 != k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3)))
    | k3_xboole_0(X1,X2) != k2_wellord1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_1421,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k3_xboole_0(X0,X1))
    | k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))) != k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3)))
    | k3_xboole_0(X0,X1) != k2_wellord1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_3274,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)))
    | k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))) != k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3)))
    | k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)) != k2_wellord1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1421])).

cnf(c_1536,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)))
    | r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_306,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1422,plain,
    ( k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))) = k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_1096,plain,
    ( k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))) = k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_771,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | X0 != k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3)))
    | X1 != k2_wellord1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_911,plain,
    ( r2_hidden(X0,k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)))
    | ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | X0 != k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3)))
    | k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)) != k2_wellord1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_1095,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)))
    | k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))) != k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3)))
    | k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)) != k2_wellord1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_911])).

cnf(c_11,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X1,X0),X2)
    | ~ v4_relat_2(X2)
    | ~ v1_relat_1(X2)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1016,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),X0)
    | ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),X0)
    | ~ v4_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK1(k2_wellord1(sK4,sK3)) = sK2(k2_wellord1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1018,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),sK4)
    | ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),sK4)
    | ~ v4_relat_2(sK4)
    | ~ v1_relat_1(sK4)
    | sK1(k2_wellord1(sK4,sK3)) = sK2(k2_wellord1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_1016])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_912,plain,
    ( ~ v1_relat_1(sK4)
    | k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)) = k2_wellord1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_832,plain,
    ( sK2(k2_wellord1(sK4,sK3)) = sK2(k2_wellord1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_307,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_759,plain,
    ( sK2(k2_wellord1(sK4,sK3)) != X0
    | sK2(k2_wellord1(sK4,sK3)) = sK1(k2_wellord1(sK4,sK3))
    | sK1(k2_wellord1(sK4,sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_831,plain,
    ( sK2(k2_wellord1(sK4,sK3)) != sK2(k2_wellord1(sK4,sK3))
    | sK2(k2_wellord1(sK4,sK3)) = sK1(k2_wellord1(sK4,sK3))
    | sK1(k2_wellord1(sK4,sK3)) != sK2(k2_wellord1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_724,plain,
    ( v1_relat_1(k2_wellord1(sK4,sK3))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( v4_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK2(X0) != sK1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_12,negated_conjecture,
    ( ~ v4_relat_2(k2_wellord1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_245,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(sK4,sK3) != X0
    | sK2(X0) != sK1(X0) ),
    inference(resolution_lifted,[status(thm)],[c_8,c_12])).

cnf(c_246,plain,
    ( ~ v1_relat_1(k2_wellord1(sK4,sK3))
    | sK2(k2_wellord1(sK4,sK3)) != sK1(k2_wellord1(sK4,sK3)) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_9,plain,
    ( r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
    | v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_235,plain,
    ( r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
    | ~ v1_relat_1(X0)
    | k2_wellord1(sK4,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_12])).

cnf(c_236,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | ~ v1_relat_1(k2_wellord1(sK4,sK3)) ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_10,plain,
    ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
    | v4_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_225,plain,
    ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
    | ~ v1_relat_1(X0)
    | k2_wellord1(sK4,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_226,plain,
    ( r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | ~ v1_relat_1(k2_wellord1(sK4,sK3)) ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_13,negated_conjecture,
    ( v4_relat_2(sK4) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7339,c_3274,c_1536,c_1422,c_1096,c_1095,c_1018,c_912,c_832,c_831,c_724,c_246,c_236,c_226,c_13,c_14])).


%------------------------------------------------------------------------------
