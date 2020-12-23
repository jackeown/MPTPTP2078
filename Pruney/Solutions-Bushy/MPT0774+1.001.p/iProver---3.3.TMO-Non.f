%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0774+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:06 EST 2020

% Result     : Timeout 59.24s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  109 ( 215 expanded)
%              Number of clauses        :   65 (  78 expanded)
%              Number of leaves         :   13 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  423 (1033 expanded)
%              Number of equality atoms :   78 ( 146 expanded)
%              Maximal formula depth    :   12 (   5 average)
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

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f25])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
        & sK1(X0) != sK2(X0)
        & r2_hidden(sK2(X0),k3_relat_1(X0))
        & r2_hidden(sK1(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
            & sK1(X0) != sK2(X0)
            & r2_hidden(sK2(X0),k3_relat_1(X0))
            & r2_hidden(sK1(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f23])).

fof(f37,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k4_tarski(X4,X3),X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
       => v6_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v6_relat_2(X1)
         => v6_relat_2(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ v6_relat_2(k2_wellord1(X1,X0))
      & v6_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ v6_relat_2(k2_wellord1(X1,X0))
      & v6_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ~ v6_relat_2(k2_wellord1(X1,X0))
        & v6_relat_2(X1)
        & v1_relat_1(X1) )
   => ( ~ v6_relat_2(k2_wellord1(sK4,sK3))
      & v6_relat_2(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ v6_relat_2(k2_wellord1(sK4,sK3))
    & v6_relat_2(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f15,f27])).

fof(f50,plain,(
    ~ v6_relat_2(k2_wellord1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | sK1(X0) != sK2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | r2_hidden(sK2(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | r2_hidden(sK1(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    v6_relat_2(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f48,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_507,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_107257,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))) != X0
    | k2_wellord1(sK4,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_120548,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)))
    | r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))) != X0
    | k2_wellord1(sK4,sK3) != k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_107257])).

cnf(c_151502,plain,
    ( r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)))
    | k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))) != k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3)))
    | k2_wellord1(sK4,sK3) != k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_120548])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_133595,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),X0)
    | ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),X1)
    | r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k3_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_151500,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k2_zfmisc_1(sK3,sK3))
    | r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)))
    | ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),sK4) ),
    inference(instantiation,[status(thm)],[c_133595])).

cnf(c_107233,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))) != X0
    | k2_wellord1(sK4,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_120549,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)))
    | r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))) != X0
    | k2_wellord1(sK4,sK3) != k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_107233])).

cnf(c_131724,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)))
    | k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))) != k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3)))
    | k2_wellord1(sK4,sK3) != k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_120549])).

cnf(c_128044,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),X0)
    | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),X1)
    | r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k3_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_131723,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k2_zfmisc_1(sK3,sK3))
    | r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)))
    | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),sK4) ),
    inference(instantiation,[status(thm)],[c_128044])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_23744,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k2_zfmisc_1(X0,X1))
    | ~ r2_hidden(sK1(k2_wellord1(sK4,sK3)),X1)
    | ~ r2_hidden(sK2(k2_wellord1(sK4,sK3)),X0) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_59313,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k2_zfmisc_1(X0,sK3))
    | ~ r2_hidden(sK1(k2_wellord1(sK4,sK3)),sK3)
    | ~ r2_hidden(sK2(k2_wellord1(sK4,sK3)),X0) ),
    inference(instantiation,[status(thm)],[c_23744])).

cnf(c_74729,plain,
    ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k2_zfmisc_1(sK3,sK3))
    | ~ r2_hidden(sK1(k2_wellord1(sK4,sK3)),sK3)
    | ~ r2_hidden(sK2(k2_wellord1(sK4,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_59313])).

cnf(c_23640,plain,
    ( r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k2_zfmisc_1(X0,X1))
    | ~ r2_hidden(sK1(k2_wellord1(sK4,sK3)),X0)
    | ~ r2_hidden(sK2(k2_wellord1(sK4,sK3)),X1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_59201,plain,
    ( r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k2_zfmisc_1(sK3,X0))
    | ~ r2_hidden(sK1(k2_wellord1(sK4,sK3)),sK3)
    | ~ r2_hidden(sK2(k2_wellord1(sK4,sK3)),X0) ),
    inference(instantiation,[status(thm)],[c_23640])).

cnf(c_74713,plain,
    ( r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k2_zfmisc_1(sK3,sK3))
    | ~ r2_hidden(sK1(k2_wellord1(sK4,sK3)),sK3)
    | ~ r2_hidden(sK2(k2_wellord1(sK4,sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_59201])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X2,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X2,X0),X1)
    | r2_hidden(k4_tarski(X0,X2),X1)
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X2 = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3714,plain,
    ( ~ r2_hidden(X0,k3_relat_1(X1))
    | r2_hidden(k4_tarski(X0,sK1(k2_wellord1(sK4,sK3))),X1)
    | r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),X0),X1)
    | ~ r2_hidden(sK1(k2_wellord1(sK4,sK3)),k3_relat_1(X1))
    | ~ v6_relat_2(X1)
    | ~ v1_relat_1(X1)
    | X0 = sK1(k2_wellord1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_68451,plain,
    ( r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),sK4)
    | r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),sK4)
    | ~ r2_hidden(sK1(k2_wellord1(sK4,sK3)),k3_relat_1(sK4))
    | ~ r2_hidden(sK2(k2_wellord1(sK4,sK3)),k3_relat_1(sK4))
    | ~ v6_relat_2(sK4)
    | ~ v1_relat_1(sK4)
    | sK2(k2_wellord1(sK4,sK3)) = sK1(k2_wellord1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_3714])).

cnf(c_18,plain,
    ( r2_hidden(X0,k3_relat_1(X1))
    | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X1,X2)))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_7024,plain,
    ( r2_hidden(sK2(k2_wellord1(sK4,sK3)),k3_relat_1(X0))
    | ~ r2_hidden(sK2(k2_wellord1(sK4,sK3)),k3_relat_1(k2_wellord1(X0,X1)))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_31782,plain,
    ( ~ r2_hidden(sK2(k2_wellord1(sK4,sK3)),k3_relat_1(k2_wellord1(sK4,sK3)))
    | r2_hidden(sK2(k2_wellord1(sK4,sK3)),k3_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7024])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_31518,plain,
    ( ~ v1_relat_1(sK4)
    | k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)) = k2_wellord1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_17,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_7338,plain,
    ( ~ r2_hidden(sK2(k2_wellord1(sK4,sK3)),k3_relat_1(k2_wellord1(sK4,sK3)))
    | r2_hidden(sK2(k2_wellord1(sK4,sK3)),sK3)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_7335,plain,
    ( ~ r2_hidden(sK1(k2_wellord1(sK4,sK3)),k3_relat_1(k2_wellord1(sK4,sK3)))
    | r2_hidden(sK1(k2_wellord1(sK4,sK3)),sK3)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_505,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_945,plain,
    ( X0 != X1
    | k2_wellord1(sK4,sK3) != X1
    | k2_wellord1(sK4,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_1446,plain,
    ( X0 != k2_wellord1(sK4,sK3)
    | k2_wellord1(sK4,sK3) = X0
    | k2_wellord1(sK4,sK3) != k2_wellord1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_945])).

cnf(c_4457,plain,
    ( k2_wellord1(sK4,sK3) != k2_wellord1(sK4,sK3)
    | k2_wellord1(sK4,sK3) = k3_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k2_wellord1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1446])).

cnf(c_7173,plain,
    ( k2_wellord1(sK4,sK3) != k2_wellord1(sK4,sK3)
    | k2_wellord1(sK4,sK3) = k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3))
    | k3_xboole_0(sK4,k2_zfmisc_1(sK3,sK3)) != k2_wellord1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_4457])).

cnf(c_504,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4710,plain,
    ( k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))) = k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))) ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_4418,plain,
    ( k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))) = k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))) ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_1544,plain,
    ( r2_hidden(sK1(k2_wellord1(sK4,sK3)),k3_relat_1(X0))
    | ~ r2_hidden(sK1(k2_wellord1(sK4,sK3)),k3_relat_1(k2_wellord1(X0,X1)))
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3296,plain,
    ( ~ r2_hidden(sK1(k2_wellord1(sK4,sK3)),k3_relat_1(k2_wellord1(sK4,sK3)))
    | r2_hidden(sK1(k2_wellord1(sK4,sK3)),k3_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1544])).

cnf(c_2041,plain,
    ( k2_wellord1(sK4,sK3) = k2_wellord1(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_2038,plain,
    ( sK1(k2_wellord1(sK4,sK3)) = sK1(k2_wellord1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_504])).

cnf(c_1021,plain,
    ( sK1(k2_wellord1(sK4,sK3)) != X0
    | sK1(k2_wellord1(sK4,sK3)) = sK2(k2_wellord1(sK4,sK3))
    | sK2(k2_wellord1(sK4,sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_505])).

cnf(c_1491,plain,
    ( sK1(k2_wellord1(sK4,sK3)) != sK1(k2_wellord1(sK4,sK3))
    | sK1(k2_wellord1(sK4,sK3)) = sK2(k2_wellord1(sK4,sK3))
    | sK2(k2_wellord1(sK4,sK3)) != sK1(k2_wellord1(sK4,sK3)) ),
    inference(instantiation,[status(thm)],[c_1021])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_930,plain,
    ( v1_relat_1(k2_wellord1(sK4,sK3))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
    | v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,negated_conjecture,
    ( ~ v6_relat_2(k2_wellord1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_411,plain,
    ( ~ r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
    | ~ v1_relat_1(X0)
    | k2_wellord1(sK4,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_412,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK4,sK3)),sK1(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | ~ v1_relat_1(k2_wellord1(sK4,sK3)) ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_9,plain,
    ( ~ r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
    | v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_401,plain,
    ( ~ r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
    | ~ v1_relat_1(X0)
    | k2_wellord1(sK4,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_402,plain,
    ( ~ r2_hidden(k4_tarski(sK1(k2_wellord1(sK4,sK3)),sK2(k2_wellord1(sK4,sK3))),k2_wellord1(sK4,sK3))
    | ~ v1_relat_1(k2_wellord1(sK4,sK3)) ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_10,plain,
    ( v6_relat_2(X0)
    | ~ v1_relat_1(X0)
    | sK1(X0) != sK2(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_391,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(sK4,sK3) != X0
    | sK1(X0) != sK2(X0) ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_392,plain,
    ( ~ v1_relat_1(k2_wellord1(sK4,sK3))
    | sK1(k2_wellord1(sK4,sK3)) != sK2(k2_wellord1(sK4,sK3)) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_11,plain,
    ( r2_hidden(sK2(X0),k3_relat_1(X0))
    | v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_381,plain,
    ( r2_hidden(sK2(X0),k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k2_wellord1(sK4,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_382,plain,
    ( r2_hidden(sK2(k2_wellord1(sK4,sK3)),k3_relat_1(k2_wellord1(sK4,sK3)))
    | ~ v1_relat_1(k2_wellord1(sK4,sK3)) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_12,plain,
    ( r2_hidden(sK1(X0),k3_relat_1(X0))
    | v6_relat_2(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_371,plain,
    ( r2_hidden(sK1(X0),k3_relat_1(X0))
    | ~ v1_relat_1(X0)
    | k2_wellord1(sK4,sK3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_372,plain,
    ( r2_hidden(sK1(k2_wellord1(sK4,sK3)),k3_relat_1(k2_wellord1(sK4,sK3)))
    | ~ v1_relat_1(k2_wellord1(sK4,sK3)) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_20,negated_conjecture,
    ( v6_relat_2(sK4) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_151502,c_151500,c_131724,c_131723,c_74729,c_74713,c_68451,c_31782,c_31518,c_7338,c_7335,c_7173,c_4710,c_4418,c_3296,c_2041,c_2038,c_1491,c_930,c_412,c_402,c_392,c_382,c_372,c_20,c_21])).


%------------------------------------------------------------------------------
