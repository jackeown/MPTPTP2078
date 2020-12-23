%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:19 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.79s
% Verified   : 
% Statistics : Number of formulae       :  156 (1204 expanded)
%              Number of clauses        :   86 ( 476 expanded)
%              Number of leaves         :   23 ( 250 expanded)
%              Depth                    :   23
%              Number of atoms          :  407 (3382 expanded)
%              Number of equality atoms :  161 ( 948 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_xboole_0(X0,X1) )
         => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v2_funct_1(X2)
      & r1_xboole_0(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f56,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v2_funct_1(X2)
        & r1_xboole_0(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,sK9))
      & v2_funct_1(sK10)
      & r1_xboole_0(sK8,sK9)
      & v1_funct_1(sK10)
      & v1_relat_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,sK9))
    & v2_funct_1(sK10)
    & r1_xboole_0(sK8,sK9)
    & v1_funct_1(sK10)
    & v1_relat_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f42,f56])).

fof(f80,plain,(
    v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f43])).

fof(f46,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK1(X4),sK2(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK1(X4),sK2(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f46,f45])).

fof(f63,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f52,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
     => r2_hidden(sK5(X1),k1_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f52])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
                | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),X1)
                & r2_hidden(k4_tarski(X2,X3),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f49,f50])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f57])).

fof(f83,plain,(
    v2_funct_1(sK10) ),
    inference(cnf_transformation,[],[f57])).

fof(f84,plain,(
    ~ r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,sK9)) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    r1_xboole_0(sK8,sK9) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
     => r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f36,f54])).

fof(f75,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK10) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_845,plain,
    ( v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_858,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1260,plain,
    ( k7_relat_1(sK10,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_845,c_858])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_865,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_857,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1478,plain,
    ( k2_relat_1(k7_relat_1(sK10,X0)) = k9_relat_1(sK10,X0) ),
    inference(superposition,[status(thm)],[c_845,c_857])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_856,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK5(X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3029,plain,
    ( r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
    | r2_hidden(sK5(k7_relat_1(sK10,X1)),k1_relat_1(k7_relat_1(sK10,X1))) = iProver_top
    | v1_relat_1(k7_relat_1(sK10,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_856])).

cnf(c_5171,plain,
    ( r2_hidden(sK5(k7_relat_1(sK10,X0)),k1_relat_1(k7_relat_1(sK10,X0))) = iProver_top
    | v1_relat_1(k9_relat_1(sK10,X0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK10,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_865,c_3029])).

cnf(c_5411,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k9_relat_1(sK10,k1_xboole_0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK10,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_5171])).

cnf(c_5425,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k9_relat_1(sK10,k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5411,c_1260])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_869,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_867,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_xboole_0(k1_tarski(X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1588,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_869,c_867])).

cnf(c_2666,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_865,c_1588])).

cnf(c_19934,plain,
    ( v1_relat_1(k9_relat_1(sK10,k1_xboole_0)) = iProver_top
    | r2_hidden(sK5(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5425,c_2666])).

cnf(c_19935,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k9_relat_1(sK10,k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_19934])).

cnf(c_3028,plain,
    ( k9_relat_1(sK10,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1260,c_1478])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_862,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2667,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_862,c_1588])).

cnf(c_2675,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_2666,c_2667])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_852,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_15048,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2675,c_852])).

cnf(c_15063,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2666,c_15048])).

cnf(c_2854,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2666,c_858])).

cnf(c_15065,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_15063,c_2854])).

cnf(c_19938,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k2_relat_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19935,c_3028,c_15065])).

cnf(c_19941,plain,
    ( v1_relat_1(k2_relat_1(k1_xboole_0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19938,c_1588])).

cnf(c_19957,plain,
    ( k7_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_19941,c_858])).

cnf(c_19956,plain,
    ( k2_relat_1(k7_relat_1(k2_relat_1(k1_xboole_0),X0)) = k9_relat_1(k2_relat_1(k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_19941,c_857])).

cnf(c_20111,plain,
    ( r2_hidden(X0,k9_relat_1(k2_relat_1(k1_xboole_0),X1)) != iProver_top
    | r2_hidden(sK5(k7_relat_1(k2_relat_1(k1_xboole_0),X1)),k1_relat_1(k7_relat_1(k2_relat_1(k1_xboole_0),X1))) = iProver_top
    | v1_relat_1(k7_relat_1(k2_relat_1(k1_xboole_0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19956,c_856])).

cnf(c_20434,plain,
    ( r2_hidden(sK5(k7_relat_1(k2_relat_1(k1_xboole_0),X0)),k1_relat_1(k7_relat_1(k2_relat_1(k1_xboole_0),X0))) = iProver_top
    | v1_relat_1(k9_relat_1(k2_relat_1(k1_xboole_0),X0)) = iProver_top
    | v1_relat_1(k7_relat_1(k2_relat_1(k1_xboole_0),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_865,c_20111])).

cnf(c_20679,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k9_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top
    | v1_relat_1(k7_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19957,c_20434])).

cnf(c_20693,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k9_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20679,c_15065,c_19957])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK10) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_22,negated_conjecture,
    ( ~ r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,sK9)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1054,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8))
    | r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,sK9)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1183,plain,
    ( r1_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8))
    | ~ r1_xboole_0(k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)),k9_relat_1(sK10,sK8)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_377,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1228,plain,
    ( k9_relat_1(sK10,sK8) = k9_relat_1(sK10,sK8) ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_1418,plain,
    ( r1_xboole_0(k9_relat_1(sK10,sK8),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_379,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1317,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)),k9_relat_1(sK10,sK8))
    | k9_relat_1(sK10,sK8) != X1
    | k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)) != X0 ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_1580,plain,
    ( ~ r1_xboole_0(X0,k9_relat_1(sK10,sK8))
    | r1_xboole_0(k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)),k9_relat_1(sK10,sK8))
    | k9_relat_1(sK10,sK8) != k9_relat_1(sK10,sK8)
    | k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)) != X0 ),
    inference(instantiation,[status(thm)],[c_1317])).

cnf(c_2264,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK10,k3_xboole_0(sK9,sK8)),k9_relat_1(sK10,sK8))
    | r1_xboole_0(k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)),k9_relat_1(sK10,sK8))
    | k9_relat_1(sK10,sK8) != k9_relat_1(sK10,sK8)
    | k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)) != k9_relat_1(sK10,k3_xboole_0(sK9,sK8)) ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1141,plain,
    ( ~ v1_funct_1(sK10)
    | ~ v2_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | k3_xboole_0(k9_relat_1(sK10,X0),k9_relat_1(sK10,X1)) = k9_relat_1(sK10,k3_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2265,plain,
    ( ~ v1_funct_1(sK10)
    | ~ v2_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)) = k9_relat_1(sK10,k3_xboole_0(sK9,sK8)) ),
    inference(instantiation,[status(thm)],[c_1141])).

cnf(c_1843,plain,
    ( r1_xboole_0(X0,k9_relat_1(sK10,sK8))
    | ~ r1_xboole_0(k9_relat_1(sK10,sK8),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3349,plain,
    ( r1_xboole_0(k9_relat_1(sK10,k3_xboole_0(sK9,sK8)),k9_relat_1(sK10,sK8))
    | ~ r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,k3_xboole_0(sK9,sK8))) ),
    inference(instantiation,[status(thm)],[c_1843])).

cnf(c_1423,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k9_relat_1(sK10,sK8),X2)
    | X2 != X1
    | k9_relat_1(sK10,sK8) != X0 ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_1999,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK10,sK8),X0)
    | r1_xboole_0(k9_relat_1(sK10,sK8),X1)
    | X1 != X0
    | k9_relat_1(sK10,sK8) != k9_relat_1(sK10,sK8) ),
    inference(instantiation,[status(thm)],[c_1423])).

cnf(c_3743,plain,
    ( ~ r1_xboole_0(k9_relat_1(sK10,sK8),X0)
    | r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,k3_xboole_0(sK9,sK8)))
    | k9_relat_1(sK10,k3_xboole_0(sK9,sK8)) != X0
    | k9_relat_1(sK10,sK8) != k9_relat_1(sK10,sK8) ),
    inference(instantiation,[status(thm)],[c_1999])).

cnf(c_3745,plain,
    ( r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,k3_xboole_0(sK9,sK8)))
    | ~ r1_xboole_0(k9_relat_1(sK10,sK8),k1_xboole_0)
    | k9_relat_1(sK10,k3_xboole_0(sK9,sK8)) != k1_xboole_0
    | k9_relat_1(sK10,sK8) != k9_relat_1(sK10,sK8) ),
    inference(instantiation,[status(thm)],[c_3743])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_859,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1667,plain,
    ( k7_relat_1(sK10,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(sK10,X0),X1) ),
    inference(superposition,[status(thm)],[c_845,c_859])).

cnf(c_24,negated_conjecture,
    ( r1_xboole_0(sK8,sK9) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_847,plain,
    ( r1_xboole_0(sK8,sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_870,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1467,plain,
    ( r1_xboole_0(sK9,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_847,c_870])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_855,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
    | r1_xboole_0(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2480,plain,
    ( k7_relat_1(k7_relat_1(X0,sK9),sK8) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1467,c_855])).

cnf(c_4094,plain,
    ( k7_relat_1(k7_relat_1(sK10,sK9),sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_845,c_2480])).

cnf(c_4310,plain,
    ( k7_relat_1(sK10,k3_xboole_0(sK9,sK8)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1667,c_4094])).

cnf(c_17,plain,
    ( r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
    | ~ v1_relat_1(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_853,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5173,plain,
    ( k9_relat_1(sK10,X0) = k1_xboole_0
    | r2_hidden(sK5(k7_relat_1(sK10,X0)),k1_relat_1(k7_relat_1(sK10,X0))) = iProver_top
    | v1_relat_1(k9_relat_1(sK10,X0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK10,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_853,c_3029])).

cnf(c_5206,plain,
    ( k9_relat_1(sK10,X0) = k1_xboole_0
    | r2_hidden(sK5(k7_relat_1(sK10,X0)),k1_relat_1(k7_relat_1(sK10,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK10,X0)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5171,c_5173])).

cnf(c_19012,plain,
    ( k9_relat_1(sK10,k3_xboole_0(sK9,sK8)) = k1_xboole_0
    | r2_hidden(sK5(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k7_relat_1(sK10,k3_xboole_0(sK9,sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4310,c_5206])).

cnf(c_19025,plain,
    ( k9_relat_1(sK10,k3_xboole_0(sK9,sK8)) = k1_xboole_0
    | r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19012,c_4310,c_15065])).

cnf(c_28760,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20693,c_26,c_25,c_23,c_22,c_1054,c_1183,c_1228,c_1418,c_2264,c_2265,c_2666,c_3349,c_3745,c_19025])).

cnf(c_28765,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_28760,c_1588])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:24:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.79/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.79/1.50  
% 7.79/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.79/1.50  
% 7.79/1.50  ------  iProver source info
% 7.79/1.50  
% 7.79/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.79/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.79/1.50  git: non_committed_changes: false
% 7.79/1.50  git: last_make_outside_of_git: false
% 7.79/1.50  
% 7.79/1.50  ------ 
% 7.79/1.50  
% 7.79/1.50  ------ Input Options
% 7.79/1.50  
% 7.79/1.50  --out_options                           all
% 7.79/1.50  --tptp_safe_out                         true
% 7.79/1.50  --problem_path                          ""
% 7.79/1.50  --include_path                          ""
% 7.79/1.50  --clausifier                            res/vclausify_rel
% 7.79/1.50  --clausifier_options                    --mode clausify
% 7.79/1.50  --stdin                                 false
% 7.79/1.50  --stats_out                             sel
% 7.79/1.50  
% 7.79/1.50  ------ General Options
% 7.79/1.50  
% 7.79/1.50  --fof                                   false
% 7.79/1.50  --time_out_real                         604.99
% 7.79/1.50  --time_out_virtual                      -1.
% 7.79/1.50  --symbol_type_check                     false
% 7.79/1.50  --clausify_out                          false
% 7.79/1.50  --sig_cnt_out                           false
% 7.79/1.50  --trig_cnt_out                          false
% 7.79/1.50  --trig_cnt_out_tolerance                1.
% 7.79/1.50  --trig_cnt_out_sk_spl                   false
% 7.79/1.50  --abstr_cl_out                          false
% 7.79/1.50  
% 7.79/1.50  ------ Global Options
% 7.79/1.50  
% 7.79/1.50  --schedule                              none
% 7.79/1.50  --add_important_lit                     false
% 7.79/1.50  --prop_solver_per_cl                    1000
% 7.79/1.50  --min_unsat_core                        false
% 7.79/1.50  --soft_assumptions                      false
% 7.79/1.50  --soft_lemma_size                       3
% 7.79/1.50  --prop_impl_unit_size                   0
% 7.79/1.50  --prop_impl_unit                        []
% 7.79/1.50  --share_sel_clauses                     true
% 7.79/1.50  --reset_solvers                         false
% 7.79/1.50  --bc_imp_inh                            [conj_cone]
% 7.79/1.50  --conj_cone_tolerance                   3.
% 7.79/1.50  --extra_neg_conj                        none
% 7.79/1.50  --large_theory_mode                     true
% 7.79/1.50  --prolific_symb_bound                   200
% 7.79/1.50  --lt_threshold                          2000
% 7.79/1.50  --clause_weak_htbl                      true
% 7.79/1.50  --gc_record_bc_elim                     false
% 7.79/1.50  
% 7.79/1.50  ------ Preprocessing Options
% 7.79/1.50  
% 7.79/1.50  --preprocessing_flag                    true
% 7.79/1.50  --time_out_prep_mult                    0.1
% 7.79/1.50  --splitting_mode                        input
% 7.79/1.50  --splitting_grd                         true
% 7.79/1.50  --splitting_cvd                         false
% 7.79/1.50  --splitting_cvd_svl                     false
% 7.79/1.50  --splitting_nvd                         32
% 7.79/1.50  --sub_typing                            true
% 7.79/1.50  --prep_gs_sim                           false
% 7.79/1.50  --prep_unflatten                        true
% 7.79/1.50  --prep_res_sim                          true
% 7.79/1.50  --prep_upred                            true
% 7.79/1.50  --prep_sem_filter                       exhaustive
% 7.79/1.50  --prep_sem_filter_out                   false
% 7.79/1.50  --pred_elim                             false
% 7.79/1.50  --res_sim_input                         true
% 7.79/1.50  --eq_ax_congr_red                       true
% 7.79/1.50  --pure_diseq_elim                       true
% 7.79/1.50  --brand_transform                       false
% 7.79/1.50  --non_eq_to_eq                          false
% 7.79/1.50  --prep_def_merge                        true
% 7.79/1.50  --prep_def_merge_prop_impl              false
% 7.79/1.50  --prep_def_merge_mbd                    true
% 7.79/1.50  --prep_def_merge_tr_red                 false
% 7.79/1.50  --prep_def_merge_tr_cl                  false
% 7.79/1.50  --smt_preprocessing                     true
% 7.79/1.50  --smt_ac_axioms                         fast
% 7.79/1.50  --preprocessed_out                      false
% 7.79/1.50  --preprocessed_stats                    false
% 7.79/1.50  
% 7.79/1.50  ------ Abstraction refinement Options
% 7.79/1.50  
% 7.79/1.50  --abstr_ref                             []
% 7.79/1.50  --abstr_ref_prep                        false
% 7.79/1.50  --abstr_ref_until_sat                   false
% 7.79/1.50  --abstr_ref_sig_restrict                funpre
% 7.79/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.79/1.50  --abstr_ref_under                       []
% 7.79/1.50  
% 7.79/1.50  ------ SAT Options
% 7.79/1.50  
% 7.79/1.50  --sat_mode                              false
% 7.79/1.50  --sat_fm_restart_options                ""
% 7.79/1.50  --sat_gr_def                            false
% 7.79/1.50  --sat_epr_types                         true
% 7.79/1.50  --sat_non_cyclic_types                  false
% 7.79/1.50  --sat_finite_models                     false
% 7.79/1.50  --sat_fm_lemmas                         false
% 7.79/1.50  --sat_fm_prep                           false
% 7.79/1.50  --sat_fm_uc_incr                        true
% 7.79/1.50  --sat_out_model                         small
% 7.79/1.50  --sat_out_clauses                       false
% 7.79/1.50  
% 7.79/1.50  ------ QBF Options
% 7.79/1.50  
% 7.79/1.50  --qbf_mode                              false
% 7.79/1.50  --qbf_elim_univ                         false
% 7.79/1.50  --qbf_dom_inst                          none
% 7.79/1.50  --qbf_dom_pre_inst                      false
% 7.79/1.50  --qbf_sk_in                             false
% 7.79/1.50  --qbf_pred_elim                         true
% 7.79/1.50  --qbf_split                             512
% 7.79/1.50  
% 7.79/1.50  ------ BMC1 Options
% 7.79/1.50  
% 7.79/1.50  --bmc1_incremental                      false
% 7.79/1.50  --bmc1_axioms                           reachable_all
% 7.79/1.50  --bmc1_min_bound                        0
% 7.79/1.50  --bmc1_max_bound                        -1
% 7.79/1.50  --bmc1_max_bound_default                -1
% 7.79/1.50  --bmc1_symbol_reachability              true
% 7.79/1.50  --bmc1_property_lemmas                  false
% 7.79/1.50  --bmc1_k_induction                      false
% 7.79/1.50  --bmc1_non_equiv_states                 false
% 7.79/1.50  --bmc1_deadlock                         false
% 7.79/1.50  --bmc1_ucm                              false
% 7.79/1.50  --bmc1_add_unsat_core                   none
% 7.79/1.50  --bmc1_unsat_core_children              false
% 7.79/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.79/1.50  --bmc1_out_stat                         full
% 7.79/1.50  --bmc1_ground_init                      false
% 7.79/1.50  --bmc1_pre_inst_next_state              false
% 7.79/1.50  --bmc1_pre_inst_state                   false
% 7.79/1.50  --bmc1_pre_inst_reach_state             false
% 7.79/1.50  --bmc1_out_unsat_core                   false
% 7.79/1.50  --bmc1_aig_witness_out                  false
% 7.79/1.50  --bmc1_verbose                          false
% 7.79/1.50  --bmc1_dump_clauses_tptp                false
% 7.79/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.79/1.50  --bmc1_dump_file                        -
% 7.79/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.79/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.79/1.50  --bmc1_ucm_extend_mode                  1
% 7.79/1.50  --bmc1_ucm_init_mode                    2
% 7.79/1.50  --bmc1_ucm_cone_mode                    none
% 7.79/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.79/1.50  --bmc1_ucm_relax_model                  4
% 7.79/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.79/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.79/1.50  --bmc1_ucm_layered_model                none
% 7.79/1.50  --bmc1_ucm_max_lemma_size               10
% 7.79/1.50  
% 7.79/1.50  ------ AIG Options
% 7.79/1.50  
% 7.79/1.50  --aig_mode                              false
% 7.79/1.50  
% 7.79/1.50  ------ Instantiation Options
% 7.79/1.50  
% 7.79/1.50  --instantiation_flag                    true
% 7.79/1.50  --inst_sos_flag                         false
% 7.79/1.50  --inst_sos_phase                        true
% 7.79/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.79/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.79/1.50  --inst_lit_sel_side                     num_symb
% 7.79/1.50  --inst_solver_per_active                1400
% 7.79/1.50  --inst_solver_calls_frac                1.
% 7.79/1.50  --inst_passive_queue_type               priority_queues
% 7.79/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.79/1.50  --inst_passive_queues_freq              [25;2]
% 7.79/1.50  --inst_dismatching                      true
% 7.79/1.50  --inst_eager_unprocessed_to_passive     true
% 7.79/1.50  --inst_prop_sim_given                   true
% 7.79/1.50  --inst_prop_sim_new                     false
% 7.79/1.50  --inst_subs_new                         false
% 7.79/1.50  --inst_eq_res_simp                      false
% 7.79/1.50  --inst_subs_given                       false
% 7.79/1.50  --inst_orphan_elimination               true
% 7.79/1.50  --inst_learning_loop_flag               true
% 7.79/1.50  --inst_learning_start                   3000
% 7.79/1.50  --inst_learning_factor                  2
% 7.79/1.50  --inst_start_prop_sim_after_learn       3
% 7.79/1.50  --inst_sel_renew                        solver
% 7.79/1.50  --inst_lit_activity_flag                true
% 7.79/1.50  --inst_restr_to_given                   false
% 7.79/1.50  --inst_activity_threshold               500
% 7.79/1.50  --inst_out_proof                        true
% 7.79/1.50  
% 7.79/1.50  ------ Resolution Options
% 7.79/1.50  
% 7.79/1.50  --resolution_flag                       true
% 7.79/1.50  --res_lit_sel                           adaptive
% 7.79/1.50  --res_lit_sel_side                      none
% 7.79/1.50  --res_ordering                          kbo
% 7.79/1.50  --res_to_prop_solver                    active
% 7.79/1.50  --res_prop_simpl_new                    false
% 7.79/1.50  --res_prop_simpl_given                  true
% 7.79/1.50  --res_passive_queue_type                priority_queues
% 7.79/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.79/1.50  --res_passive_queues_freq               [15;5]
% 7.79/1.50  --res_forward_subs                      full
% 7.79/1.50  --res_backward_subs                     full
% 7.79/1.50  --res_forward_subs_resolution           true
% 7.79/1.50  --res_backward_subs_resolution          true
% 7.79/1.50  --res_orphan_elimination                true
% 7.79/1.50  --res_time_limit                        2.
% 7.79/1.50  --res_out_proof                         true
% 7.79/1.50  
% 7.79/1.50  ------ Superposition Options
% 7.79/1.50  
% 7.79/1.50  --superposition_flag                    true
% 7.79/1.50  --sup_passive_queue_type                priority_queues
% 7.79/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.79/1.50  --sup_passive_queues_freq               [1;4]
% 7.79/1.50  --demod_completeness_check              fast
% 7.79/1.50  --demod_use_ground                      true
% 7.79/1.50  --sup_to_prop_solver                    passive
% 7.79/1.50  --sup_prop_simpl_new                    true
% 7.79/1.50  --sup_prop_simpl_given                  true
% 7.79/1.50  --sup_fun_splitting                     false
% 7.79/1.50  --sup_smt_interval                      50000
% 7.79/1.50  
% 7.79/1.50  ------ Superposition Simplification Setup
% 7.79/1.50  
% 7.79/1.50  --sup_indices_passive                   []
% 7.79/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.79/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.50  --sup_full_bw                           [BwDemod]
% 7.79/1.50  --sup_immed_triv                        [TrivRules]
% 7.79/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.50  --sup_immed_bw_main                     []
% 7.79/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.79/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.79/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.79/1.50  
% 7.79/1.50  ------ Combination Options
% 7.79/1.50  
% 7.79/1.50  --comb_res_mult                         3
% 7.79/1.50  --comb_sup_mult                         2
% 7.79/1.50  --comb_inst_mult                        10
% 7.79/1.50  
% 7.79/1.50  ------ Debug Options
% 7.79/1.50  
% 7.79/1.50  --dbg_backtrace                         false
% 7.79/1.50  --dbg_dump_prop_clauses                 false
% 7.79/1.50  --dbg_dump_prop_clauses_file            -
% 7.79/1.50  --dbg_out_stat                          false
% 7.79/1.50  ------ Parsing...
% 7.79/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.79/1.50  
% 7.79/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.79/1.50  
% 7.79/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.79/1.50  
% 7.79/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.79/1.50  ------ Proving...
% 7.79/1.50  ------ Problem Properties 
% 7.79/1.50  
% 7.79/1.50  
% 7.79/1.50  clauses                                 26
% 7.79/1.50  conjectures                             5
% 7.79/1.50  EPR                                     6
% 7.79/1.50  Horn                                    23
% 7.79/1.50  unary                                   8
% 7.79/1.50  binary                                  8
% 7.79/1.50  lits                                    56
% 7.79/1.50  lits eq                                 10
% 7.79/1.50  fd_pure                                 0
% 7.79/1.50  fd_pseudo                               0
% 7.79/1.50  fd_cond                                 1
% 7.79/1.50  fd_pseudo_cond                          0
% 7.79/1.50  AC symbols                              0
% 7.79/1.50  
% 7.79/1.50  ------ Input Options Time Limit: Unbounded
% 7.79/1.50  
% 7.79/1.50  
% 7.79/1.50  ------ 
% 7.79/1.50  Current options:
% 7.79/1.50  ------ 
% 7.79/1.50  
% 7.79/1.50  ------ Input Options
% 7.79/1.50  
% 7.79/1.50  --out_options                           all
% 7.79/1.50  --tptp_safe_out                         true
% 7.79/1.50  --problem_path                          ""
% 7.79/1.50  --include_path                          ""
% 7.79/1.50  --clausifier                            res/vclausify_rel
% 7.79/1.50  --clausifier_options                    --mode clausify
% 7.79/1.50  --stdin                                 false
% 7.79/1.50  --stats_out                             sel
% 7.79/1.50  
% 7.79/1.50  ------ General Options
% 7.79/1.50  
% 7.79/1.50  --fof                                   false
% 7.79/1.50  --time_out_real                         604.99
% 7.79/1.50  --time_out_virtual                      -1.
% 7.79/1.50  --symbol_type_check                     false
% 7.79/1.50  --clausify_out                          false
% 7.79/1.50  --sig_cnt_out                           false
% 7.79/1.50  --trig_cnt_out                          false
% 7.79/1.50  --trig_cnt_out_tolerance                1.
% 7.79/1.50  --trig_cnt_out_sk_spl                   false
% 7.79/1.50  --abstr_cl_out                          false
% 7.79/1.50  
% 7.79/1.50  ------ Global Options
% 7.79/1.50  
% 7.79/1.50  --schedule                              none
% 7.79/1.50  --add_important_lit                     false
% 7.79/1.50  --prop_solver_per_cl                    1000
% 7.79/1.50  --min_unsat_core                        false
% 7.79/1.50  --soft_assumptions                      false
% 7.79/1.50  --soft_lemma_size                       3
% 7.79/1.50  --prop_impl_unit_size                   0
% 7.79/1.50  --prop_impl_unit                        []
% 7.79/1.50  --share_sel_clauses                     true
% 7.79/1.50  --reset_solvers                         false
% 7.79/1.50  --bc_imp_inh                            [conj_cone]
% 7.79/1.50  --conj_cone_tolerance                   3.
% 7.79/1.50  --extra_neg_conj                        none
% 7.79/1.50  --large_theory_mode                     true
% 7.79/1.50  --prolific_symb_bound                   200
% 7.79/1.50  --lt_threshold                          2000
% 7.79/1.50  --clause_weak_htbl                      true
% 7.79/1.50  --gc_record_bc_elim                     false
% 7.79/1.50  
% 7.79/1.50  ------ Preprocessing Options
% 7.79/1.50  
% 7.79/1.50  --preprocessing_flag                    true
% 7.79/1.50  --time_out_prep_mult                    0.1
% 7.79/1.50  --splitting_mode                        input
% 7.79/1.50  --splitting_grd                         true
% 7.79/1.50  --splitting_cvd                         false
% 7.79/1.50  --splitting_cvd_svl                     false
% 7.79/1.50  --splitting_nvd                         32
% 7.79/1.50  --sub_typing                            true
% 7.79/1.50  --prep_gs_sim                           false
% 7.79/1.50  --prep_unflatten                        true
% 7.79/1.50  --prep_res_sim                          true
% 7.79/1.50  --prep_upred                            true
% 7.79/1.50  --prep_sem_filter                       exhaustive
% 7.79/1.50  --prep_sem_filter_out                   false
% 7.79/1.50  --pred_elim                             false
% 7.79/1.50  --res_sim_input                         true
% 7.79/1.50  --eq_ax_congr_red                       true
% 7.79/1.50  --pure_diseq_elim                       true
% 7.79/1.50  --brand_transform                       false
% 7.79/1.50  --non_eq_to_eq                          false
% 7.79/1.50  --prep_def_merge                        true
% 7.79/1.50  --prep_def_merge_prop_impl              false
% 7.79/1.50  --prep_def_merge_mbd                    true
% 7.79/1.50  --prep_def_merge_tr_red                 false
% 7.79/1.50  --prep_def_merge_tr_cl                  false
% 7.79/1.50  --smt_preprocessing                     true
% 7.79/1.50  --smt_ac_axioms                         fast
% 7.79/1.50  --preprocessed_out                      false
% 7.79/1.50  --preprocessed_stats                    false
% 7.79/1.50  
% 7.79/1.50  ------ Abstraction refinement Options
% 7.79/1.50  
% 7.79/1.50  --abstr_ref                             []
% 7.79/1.50  --abstr_ref_prep                        false
% 7.79/1.50  --abstr_ref_until_sat                   false
% 7.79/1.50  --abstr_ref_sig_restrict                funpre
% 7.79/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.79/1.50  --abstr_ref_under                       []
% 7.79/1.50  
% 7.79/1.50  ------ SAT Options
% 7.79/1.50  
% 7.79/1.50  --sat_mode                              false
% 7.79/1.50  --sat_fm_restart_options                ""
% 7.79/1.50  --sat_gr_def                            false
% 7.79/1.50  --sat_epr_types                         true
% 7.79/1.50  --sat_non_cyclic_types                  false
% 7.79/1.50  --sat_finite_models                     false
% 7.79/1.50  --sat_fm_lemmas                         false
% 7.79/1.50  --sat_fm_prep                           false
% 7.79/1.50  --sat_fm_uc_incr                        true
% 7.79/1.50  --sat_out_model                         small
% 7.79/1.50  --sat_out_clauses                       false
% 7.79/1.50  
% 7.79/1.50  ------ QBF Options
% 7.79/1.50  
% 7.79/1.50  --qbf_mode                              false
% 7.79/1.50  --qbf_elim_univ                         false
% 7.79/1.50  --qbf_dom_inst                          none
% 7.79/1.50  --qbf_dom_pre_inst                      false
% 7.79/1.50  --qbf_sk_in                             false
% 7.79/1.50  --qbf_pred_elim                         true
% 7.79/1.50  --qbf_split                             512
% 7.79/1.50  
% 7.79/1.50  ------ BMC1 Options
% 7.79/1.50  
% 7.79/1.50  --bmc1_incremental                      false
% 7.79/1.50  --bmc1_axioms                           reachable_all
% 7.79/1.50  --bmc1_min_bound                        0
% 7.79/1.50  --bmc1_max_bound                        -1
% 7.79/1.50  --bmc1_max_bound_default                -1
% 7.79/1.50  --bmc1_symbol_reachability              true
% 7.79/1.50  --bmc1_property_lemmas                  false
% 7.79/1.50  --bmc1_k_induction                      false
% 7.79/1.50  --bmc1_non_equiv_states                 false
% 7.79/1.50  --bmc1_deadlock                         false
% 7.79/1.50  --bmc1_ucm                              false
% 7.79/1.50  --bmc1_add_unsat_core                   none
% 7.79/1.50  --bmc1_unsat_core_children              false
% 7.79/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.79/1.50  --bmc1_out_stat                         full
% 7.79/1.50  --bmc1_ground_init                      false
% 7.79/1.50  --bmc1_pre_inst_next_state              false
% 7.79/1.50  --bmc1_pre_inst_state                   false
% 7.79/1.50  --bmc1_pre_inst_reach_state             false
% 7.79/1.50  --bmc1_out_unsat_core                   false
% 7.79/1.50  --bmc1_aig_witness_out                  false
% 7.79/1.50  --bmc1_verbose                          false
% 7.79/1.50  --bmc1_dump_clauses_tptp                false
% 7.79/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.79/1.50  --bmc1_dump_file                        -
% 7.79/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.79/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.79/1.50  --bmc1_ucm_extend_mode                  1
% 7.79/1.50  --bmc1_ucm_init_mode                    2
% 7.79/1.50  --bmc1_ucm_cone_mode                    none
% 7.79/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.79/1.50  --bmc1_ucm_relax_model                  4
% 7.79/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.79/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.79/1.50  --bmc1_ucm_layered_model                none
% 7.79/1.50  --bmc1_ucm_max_lemma_size               10
% 7.79/1.50  
% 7.79/1.50  ------ AIG Options
% 7.79/1.50  
% 7.79/1.50  --aig_mode                              false
% 7.79/1.50  
% 7.79/1.50  ------ Instantiation Options
% 7.79/1.50  
% 7.79/1.50  --instantiation_flag                    true
% 7.79/1.50  --inst_sos_flag                         false
% 7.79/1.50  --inst_sos_phase                        true
% 7.79/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.79/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.79/1.50  --inst_lit_sel_side                     num_symb
% 7.79/1.50  --inst_solver_per_active                1400
% 7.79/1.50  --inst_solver_calls_frac                1.
% 7.79/1.50  --inst_passive_queue_type               priority_queues
% 7.79/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.79/1.50  --inst_passive_queues_freq              [25;2]
% 7.79/1.50  --inst_dismatching                      true
% 7.79/1.50  --inst_eager_unprocessed_to_passive     true
% 7.79/1.50  --inst_prop_sim_given                   true
% 7.79/1.50  --inst_prop_sim_new                     false
% 7.79/1.50  --inst_subs_new                         false
% 7.79/1.50  --inst_eq_res_simp                      false
% 7.79/1.50  --inst_subs_given                       false
% 7.79/1.50  --inst_orphan_elimination               true
% 7.79/1.50  --inst_learning_loop_flag               true
% 7.79/1.50  --inst_learning_start                   3000
% 7.79/1.50  --inst_learning_factor                  2
% 7.79/1.50  --inst_start_prop_sim_after_learn       3
% 7.79/1.50  --inst_sel_renew                        solver
% 7.79/1.50  --inst_lit_activity_flag                true
% 7.79/1.50  --inst_restr_to_given                   false
% 7.79/1.50  --inst_activity_threshold               500
% 7.79/1.50  --inst_out_proof                        true
% 7.79/1.50  
% 7.79/1.50  ------ Resolution Options
% 7.79/1.50  
% 7.79/1.50  --resolution_flag                       true
% 7.79/1.50  --res_lit_sel                           adaptive
% 7.79/1.50  --res_lit_sel_side                      none
% 7.79/1.50  --res_ordering                          kbo
% 7.79/1.50  --res_to_prop_solver                    active
% 7.79/1.50  --res_prop_simpl_new                    false
% 7.79/1.50  --res_prop_simpl_given                  true
% 7.79/1.50  --res_passive_queue_type                priority_queues
% 7.79/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.79/1.50  --res_passive_queues_freq               [15;5]
% 7.79/1.50  --res_forward_subs                      full
% 7.79/1.50  --res_backward_subs                     full
% 7.79/1.50  --res_forward_subs_resolution           true
% 7.79/1.50  --res_backward_subs_resolution          true
% 7.79/1.50  --res_orphan_elimination                true
% 7.79/1.50  --res_time_limit                        2.
% 7.79/1.50  --res_out_proof                         true
% 7.79/1.50  
% 7.79/1.50  ------ Superposition Options
% 7.79/1.50  
% 7.79/1.50  --superposition_flag                    true
% 7.79/1.50  --sup_passive_queue_type                priority_queues
% 7.79/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.79/1.50  --sup_passive_queues_freq               [1;4]
% 7.79/1.50  --demod_completeness_check              fast
% 7.79/1.50  --demod_use_ground                      true
% 7.79/1.50  --sup_to_prop_solver                    passive
% 7.79/1.50  --sup_prop_simpl_new                    true
% 7.79/1.50  --sup_prop_simpl_given                  true
% 7.79/1.50  --sup_fun_splitting                     false
% 7.79/1.50  --sup_smt_interval                      50000
% 7.79/1.50  
% 7.79/1.50  ------ Superposition Simplification Setup
% 7.79/1.50  
% 7.79/1.50  --sup_indices_passive                   []
% 7.79/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.79/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.79/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.50  --sup_full_bw                           [BwDemod]
% 7.79/1.50  --sup_immed_triv                        [TrivRules]
% 7.79/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.79/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.50  --sup_immed_bw_main                     []
% 7.79/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.79/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.79/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.79/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.79/1.50  
% 7.79/1.50  ------ Combination Options
% 7.79/1.50  
% 7.79/1.50  --comb_res_mult                         3
% 7.79/1.50  --comb_sup_mult                         2
% 7.79/1.50  --comb_inst_mult                        10
% 7.79/1.50  
% 7.79/1.50  ------ Debug Options
% 7.79/1.50  
% 7.79/1.50  --dbg_backtrace                         false
% 7.79/1.50  --dbg_dump_prop_clauses                 false
% 7.79/1.50  --dbg_dump_prop_clauses_file            -
% 7.79/1.50  --dbg_out_stat                          false
% 7.79/1.50  
% 7.79/1.50  
% 7.79/1.50  
% 7.79/1.50  
% 7.79/1.50  ------ Proving...
% 7.79/1.50  
% 7.79/1.50  
% 7.79/1.50  % SZS status Theorem for theBenchmark.p
% 7.79/1.50  
% 7.79/1.50   Resolution empty clause
% 7.79/1.50  
% 7.79/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.79/1.50  
% 7.79/1.50  fof(f18,conjecture,(
% 7.79/1.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 7.79/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.50  
% 7.79/1.50  fof(f19,negated_conjecture,(
% 7.79/1.50    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_xboole_0(X0,X1)) => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 7.79/1.50    inference(negated_conjecture,[],[f18])).
% 7.79/1.50  
% 7.79/1.50  fof(f41,plain,(
% 7.79/1.50    ? [X0,X1,X2] : ((~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & (v2_funct_1(X2) & r1_xboole_0(X0,X1))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 7.79/1.50    inference(ennf_transformation,[],[f19])).
% 7.79/1.50  
% 7.79/1.50  fof(f42,plain,(
% 7.79/1.50    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.79/1.50    inference(flattening,[],[f41])).
% 7.79/1.50  
% 7.79/1.50  fof(f56,plain,(
% 7.79/1.50    ? [X0,X1,X2] : (~r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v2_funct_1(X2) & r1_xboole_0(X0,X1) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,sK9)) & v2_funct_1(sK10) & r1_xboole_0(sK8,sK9) & v1_funct_1(sK10) & v1_relat_1(sK10))),
% 7.79/1.50    introduced(choice_axiom,[])).
% 7.79/1.50  
% 7.79/1.50  fof(f57,plain,(
% 7.79/1.50    ~r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,sK9)) & v2_funct_1(sK10) & r1_xboole_0(sK8,sK9) & v1_funct_1(sK10) & v1_relat_1(sK10)),
% 7.79/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f42,f56])).
% 7.79/1.50  
% 7.79/1.50  fof(f80,plain,(
% 7.79/1.50    v1_relat_1(sK10)),
% 7.79/1.50    inference(cnf_transformation,[],[f57])).
% 7.79/1.50  
% 7.79/1.50  fof(f9,axiom,(
% 7.79/1.50    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 7.79/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.50  
% 7.79/1.50  fof(f27,plain,(
% 7.79/1.50    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 7.79/1.50    inference(ennf_transformation,[],[f9])).
% 7.79/1.50  
% 7.79/1.50  fof(f70,plain,(
% 7.79/1.50    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 7.79/1.50    inference(cnf_transformation,[],[f27])).
% 7.79/1.50  
% 7.79/1.50  fof(f5,axiom,(
% 7.79/1.50    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 7.79/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.50  
% 7.79/1.50  fof(f24,plain,(
% 7.79/1.50    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 7.79/1.50    inference(ennf_transformation,[],[f5])).
% 7.79/1.50  
% 7.79/1.50  fof(f43,plain,(
% 7.79/1.50    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 7.79/1.50    inference(nnf_transformation,[],[f24])).
% 7.79/1.50  
% 7.79/1.50  fof(f44,plain,(
% 7.79/1.50    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 7.79/1.50    inference(rectify,[],[f43])).
% 7.79/1.50  
% 7.79/1.50  fof(f46,plain,(
% 7.79/1.50    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK1(X4),sK2(X4)) = X4)),
% 7.79/1.50    introduced(choice_axiom,[])).
% 7.79/1.50  
% 7.79/1.50  fof(f45,plain,(
% 7.79/1.50    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 7.79/1.50    introduced(choice_axiom,[])).
% 7.79/1.50  
% 7.79/1.50  fof(f47,plain,(
% 7.79/1.50    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0))) & (! [X4] : (k4_tarski(sK1(X4),sK2(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 7.79/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f46,f45])).
% 7.79/1.50  
% 7.79/1.50  fof(f63,plain,(
% 7.79/1.50    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) )),
% 7.79/1.50    inference(cnf_transformation,[],[f47])).
% 7.79/1.50  
% 7.79/1.50  fof(f10,axiom,(
% 7.79/1.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 7.79/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.50  
% 7.79/1.50  fof(f28,plain,(
% 7.79/1.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.79/1.50    inference(ennf_transformation,[],[f10])).
% 7.79/1.50  
% 7.79/1.50  fof(f71,plain,(
% 7.79/1.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.79/1.50    inference(cnf_transformation,[],[f28])).
% 7.79/1.50  
% 7.79/1.50  fof(f11,axiom,(
% 7.79/1.50    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 7.79/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.50  
% 7.79/1.50  fof(f29,plain,(
% 7.79/1.50    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.79/1.50    inference(ennf_transformation,[],[f11])).
% 7.79/1.50  
% 7.79/1.50  fof(f30,plain,(
% 7.79/1.50    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.79/1.50    inference(flattening,[],[f29])).
% 7.79/1.50  
% 7.79/1.50  fof(f52,plain,(
% 7.79/1.50    ! [X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(sK5(X1),k1_relat_1(X1)))),
% 7.79/1.50    introduced(choice_axiom,[])).
% 7.79/1.50  
% 7.79/1.50  fof(f53,plain,(
% 7.79/1.50    ! [X0,X1] : (r2_hidden(sK5(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.79/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f30,f52])).
% 7.79/1.50  
% 7.79/1.50  fof(f72,plain,(
% 7.79/1.50    ( ! [X0,X1] : (r2_hidden(sK5(X1),k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.79/1.50    inference(cnf_transformation,[],[f53])).
% 7.79/1.50  
% 7.79/1.50  fof(f2,axiom,(
% 7.79/1.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 7.79/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.50  
% 7.79/1.50  fof(f59,plain,(
% 7.79/1.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 7.79/1.50    inference(cnf_transformation,[],[f2])).
% 7.79/1.50  
% 7.79/1.50  fof(f4,axiom,(
% 7.79/1.50    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 7.79/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.50  
% 7.79/1.50  fof(f23,plain,(
% 7.79/1.50    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 7.79/1.50    inference(ennf_transformation,[],[f4])).
% 7.79/1.50  
% 7.79/1.50  fof(f61,plain,(
% 7.79/1.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 7.79/1.50    inference(cnf_transformation,[],[f23])).
% 7.79/1.50  
% 7.79/1.50  fof(f6,axiom,(
% 7.79/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 7.79/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.50  
% 7.79/1.50  fof(f25,plain,(
% 7.79/1.50    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 7.79/1.50    inference(ennf_transformation,[],[f6])).
% 7.79/1.50  
% 7.79/1.50  fof(f48,plain,(
% 7.79/1.50    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 7.79/1.50    inference(nnf_transformation,[],[f25])).
% 7.79/1.50  
% 7.79/1.50  fof(f49,plain,(
% 7.79/1.50    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 7.79/1.50    inference(rectify,[],[f48])).
% 7.79/1.50  
% 7.79/1.50  fof(f50,plain,(
% 7.79/1.50    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)))),
% 7.79/1.50    introduced(choice_axiom,[])).
% 7.79/1.50  
% 7.79/1.50  fof(f51,plain,(
% 7.79/1.50    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 7.79/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f49,f50])).
% 7.79/1.50  
% 7.79/1.50  fof(f66,plain,(
% 7.79/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 7.79/1.50    inference(cnf_transformation,[],[f51])).
% 7.79/1.50  
% 7.79/1.50  fof(f15,axiom,(
% 7.79/1.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.79/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.50  
% 7.79/1.50  fof(f37,plain,(
% 7.79/1.50    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.79/1.50    inference(ennf_transformation,[],[f15])).
% 7.79/1.50  
% 7.79/1.50  fof(f38,plain,(
% 7.79/1.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.79/1.50    inference(flattening,[],[f37])).
% 7.79/1.50  
% 7.79/1.50  fof(f76,plain,(
% 7.79/1.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.79/1.50    inference(cnf_transformation,[],[f38])).
% 7.79/1.50  
% 7.79/1.50  fof(f81,plain,(
% 7.79/1.50    v1_funct_1(sK10)),
% 7.79/1.50    inference(cnf_transformation,[],[f57])).
% 7.79/1.50  
% 7.79/1.50  fof(f83,plain,(
% 7.79/1.50    v2_funct_1(sK10)),
% 7.79/1.50    inference(cnf_transformation,[],[f57])).
% 7.79/1.50  
% 7.79/1.50  fof(f84,plain,(
% 7.79/1.50    ~r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,sK9))),
% 7.79/1.50    inference(cnf_transformation,[],[f57])).
% 7.79/1.50  
% 7.79/1.50  fof(f1,axiom,(
% 7.79/1.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.79/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.50  
% 7.79/1.50  fof(f21,plain,(
% 7.79/1.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.79/1.50    inference(ennf_transformation,[],[f1])).
% 7.79/1.50  
% 7.79/1.50  fof(f58,plain,(
% 7.79/1.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.79/1.50    inference(cnf_transformation,[],[f21])).
% 7.79/1.50  
% 7.79/1.50  fof(f3,axiom,(
% 7.79/1.50    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 7.79/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.50  
% 7.79/1.50  fof(f22,plain,(
% 7.79/1.50    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 7.79/1.50    inference(ennf_transformation,[],[f3])).
% 7.79/1.50  
% 7.79/1.50  fof(f60,plain,(
% 7.79/1.50    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 7.79/1.50    inference(cnf_transformation,[],[f22])).
% 7.79/1.50  
% 7.79/1.50  fof(f17,axiom,(
% 7.79/1.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1))))),
% 7.79/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.50  
% 7.79/1.50  fof(f39,plain,(
% 7.79/1.50    ! [X0,X1,X2] : ((k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.79/1.50    inference(ennf_transformation,[],[f17])).
% 7.79/1.50  
% 7.79/1.50  fof(f40,plain,(
% 7.79/1.50    ! [X0,X1,X2] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.79/1.50    inference(flattening,[],[f39])).
% 7.79/1.50  
% 7.79/1.50  fof(f79,plain,(
% 7.79/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k3_xboole_0(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.79/1.50    inference(cnf_transformation,[],[f40])).
% 7.79/1.50  
% 7.79/1.50  fof(f8,axiom,(
% 7.79/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 7.79/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.50  
% 7.79/1.50  fof(f26,plain,(
% 7.79/1.50    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.79/1.50    inference(ennf_transformation,[],[f8])).
% 7.79/1.50  
% 7.79/1.50  fof(f69,plain,(
% 7.79/1.50    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.79/1.50    inference(cnf_transformation,[],[f26])).
% 7.79/1.50  
% 7.79/1.50  fof(f82,plain,(
% 7.79/1.50    r1_xboole_0(sK8,sK9)),
% 7.79/1.50    inference(cnf_transformation,[],[f57])).
% 7.79/1.50  
% 7.79/1.50  fof(f12,axiom,(
% 7.79/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 7.79/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.50  
% 7.79/1.50  fof(f31,plain,(
% 7.79/1.50    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.79/1.50    inference(ennf_transformation,[],[f12])).
% 7.79/1.50  
% 7.79/1.50  fof(f32,plain,(
% 7.79/1.50    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 7.79/1.50    inference(flattening,[],[f31])).
% 7.79/1.50  
% 7.79/1.50  fof(f73,plain,(
% 7.79/1.50    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 7.79/1.50    inference(cnf_transformation,[],[f32])).
% 7.79/1.50  
% 7.79/1.50  fof(f14,axiom,(
% 7.79/1.50    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 7.79/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.79/1.50  
% 7.79/1.50  fof(f35,plain,(
% 7.79/1.50    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 7.79/1.50    inference(ennf_transformation,[],[f14])).
% 7.79/1.50  
% 7.79/1.50  fof(f36,plain,(
% 7.79/1.50    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 7.79/1.50    inference(flattening,[],[f35])).
% 7.79/1.50  
% 7.79/1.50  fof(f54,plain,(
% 7.79/1.50    ! [X0] : (? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) => r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0))),
% 7.79/1.50    introduced(choice_axiom,[])).
% 7.79/1.50  
% 7.79/1.50  fof(f55,plain,(
% 7.79/1.50    ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) | ~v1_relat_1(X0))),
% 7.79/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f36,f54])).
% 7.79/1.50  
% 7.79/1.50  fof(f75,plain,(
% 7.79/1.50    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) | ~v1_relat_1(X0)) )),
% 7.79/1.50    inference(cnf_transformation,[],[f55])).
% 7.79/1.50  
% 7.79/1.50  cnf(c_26,negated_conjecture,
% 7.79/1.50      ( v1_relat_1(sK10) ),
% 7.79/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_845,plain,
% 7.79/1.50      ( v1_relat_1(sK10) = iProver_top ),
% 7.79/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_12,plain,
% 7.79/1.50      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.79/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_858,plain,
% 7.79/1.50      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 7.79/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1260,plain,
% 7.79/1.50      ( k7_relat_1(sK10,k1_xboole_0) = k1_xboole_0 ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_845,c_858]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_5,plain,
% 7.79/1.50      ( r2_hidden(sK0(X0),X0) | v1_relat_1(X0) ),
% 7.79/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_865,plain,
% 7.79/1.50      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_relat_1(X0) = iProver_top ),
% 7.79/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_13,plain,
% 7.79/1.50      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 7.79/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_857,plain,
% 7.79/1.50      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 7.79/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1478,plain,
% 7.79/1.50      ( k2_relat_1(k7_relat_1(sK10,X0)) = k9_relat_1(sK10,X0) ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_845,c_857]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_14,plain,
% 7.79/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.79/1.50      | r2_hidden(sK5(X1),k1_relat_1(X1))
% 7.79/1.50      | ~ v1_relat_1(X1) ),
% 7.79/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_856,plain,
% 7.79/1.50      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 7.79/1.50      | r2_hidden(sK5(X1),k1_relat_1(X1)) = iProver_top
% 7.79/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.79/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_3029,plain,
% 7.79/1.50      ( r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
% 7.79/1.50      | r2_hidden(sK5(k7_relat_1(sK10,X1)),k1_relat_1(k7_relat_1(sK10,X1))) = iProver_top
% 7.79/1.50      | v1_relat_1(k7_relat_1(sK10,X1)) != iProver_top ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_1478,c_856]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_5171,plain,
% 7.79/1.50      ( r2_hidden(sK5(k7_relat_1(sK10,X0)),k1_relat_1(k7_relat_1(sK10,X0))) = iProver_top
% 7.79/1.50      | v1_relat_1(k9_relat_1(sK10,X0)) = iProver_top
% 7.79/1.50      | v1_relat_1(k7_relat_1(sK10,X0)) != iProver_top ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_865,c_3029]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_5411,plain,
% 7.79/1.50      ( r2_hidden(sK5(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
% 7.79/1.50      | v1_relat_1(k9_relat_1(sK10,k1_xboole_0)) = iProver_top
% 7.79/1.50      | v1_relat_1(k7_relat_1(sK10,k1_xboole_0)) != iProver_top ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_1260,c_5171]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_5425,plain,
% 7.79/1.50      ( r2_hidden(sK5(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
% 7.79/1.50      | v1_relat_1(k9_relat_1(sK10,k1_xboole_0)) = iProver_top
% 7.79/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.79/1.50      inference(light_normalisation,[status(thm)],[c_5411,c_1260]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1,plain,
% 7.79/1.50      ( r1_xboole_0(X0,k1_xboole_0) ),
% 7.79/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_869,plain,
% 7.79/1.50      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 7.79/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_3,plain,
% 7.79/1.50      ( ~ r2_hidden(X0,X1) | ~ r1_xboole_0(k1_tarski(X0),X1) ),
% 7.79/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_867,plain,
% 7.79/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.79/1.50      | r1_xboole_0(k1_tarski(X0),X1) != iProver_top ),
% 7.79/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1588,plain,
% 7.79/1.50      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_869,c_867]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_2666,plain,
% 7.79/1.50      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_865,c_1588]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_19934,plain,
% 7.79/1.50      ( v1_relat_1(k9_relat_1(sK10,k1_xboole_0)) = iProver_top
% 7.79/1.50      | r2_hidden(sK5(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top ),
% 7.79/1.50      inference(global_propositional_subsumption,[status(thm)],[c_5425,c_2666]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_19935,plain,
% 7.79/1.50      ( r2_hidden(sK5(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
% 7.79/1.50      | v1_relat_1(k9_relat_1(sK10,k1_xboole_0)) = iProver_top ),
% 7.79/1.50      inference(renaming,[status(thm)],[c_19934]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_3028,plain,
% 7.79/1.50      ( k9_relat_1(sK10,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_1260,c_1478]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_8,plain,
% 7.79/1.50      ( r1_tarski(X0,X1)
% 7.79/1.50      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
% 7.79/1.50      | ~ v1_relat_1(X0) ),
% 7.79/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_862,plain,
% 7.79/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.79/1.50      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) = iProver_top
% 7.79/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_2667,plain,
% 7.79/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top
% 7.79/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_862,c_1588]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_2675,plain,
% 7.79/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.79/1.50      inference(backward_subsumption_resolution,[status(thm)],[c_2666,c_2667]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_18,plain,
% 7.79/1.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.79/1.50      | ~ v1_relat_1(X1)
% 7.79/1.50      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 7.79/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_852,plain,
% 7.79/1.50      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 7.79/1.50      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.79/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_15048,plain,
% 7.79/1.50      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 7.79/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_2675,c_852]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_15063,plain,
% 7.79/1.50      ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_2666,c_15048]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_2854,plain,
% 7.79/1.50      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_2666,c_858]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_15065,plain,
% 7.79/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.79/1.50      inference(light_normalisation,[status(thm)],[c_15063,c_2854]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_19938,plain,
% 7.79/1.50      ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top
% 7.79/1.50      | v1_relat_1(k2_relat_1(k1_xboole_0)) = iProver_top ),
% 7.79/1.50      inference(light_normalisation,[status(thm)],[c_19935,c_3028,c_15065]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_19941,plain,
% 7.79/1.50      ( v1_relat_1(k2_relat_1(k1_xboole_0)) = iProver_top ),
% 7.79/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_19938,c_1588]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_19957,plain,
% 7.79/1.50      ( k7_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_19941,c_858]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_19956,plain,
% 7.79/1.50      ( k2_relat_1(k7_relat_1(k2_relat_1(k1_xboole_0),X0)) = k9_relat_1(k2_relat_1(k1_xboole_0),X0) ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_19941,c_857]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_20111,plain,
% 7.79/1.50      ( r2_hidden(X0,k9_relat_1(k2_relat_1(k1_xboole_0),X1)) != iProver_top
% 7.79/1.50      | r2_hidden(sK5(k7_relat_1(k2_relat_1(k1_xboole_0),X1)),k1_relat_1(k7_relat_1(k2_relat_1(k1_xboole_0),X1))) = iProver_top
% 7.79/1.50      | v1_relat_1(k7_relat_1(k2_relat_1(k1_xboole_0),X1)) != iProver_top ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_19956,c_856]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_20434,plain,
% 7.79/1.50      ( r2_hidden(sK5(k7_relat_1(k2_relat_1(k1_xboole_0),X0)),k1_relat_1(k7_relat_1(k2_relat_1(k1_xboole_0),X0))) = iProver_top
% 7.79/1.50      | v1_relat_1(k9_relat_1(k2_relat_1(k1_xboole_0),X0)) = iProver_top
% 7.79/1.50      | v1_relat_1(k7_relat_1(k2_relat_1(k1_xboole_0),X0)) != iProver_top ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_865,c_20111]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_20679,plain,
% 7.79/1.50      ( r2_hidden(sK5(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
% 7.79/1.50      | v1_relat_1(k9_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top
% 7.79/1.50      | v1_relat_1(k7_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0)) != iProver_top ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_19957,c_20434]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_20693,plain,
% 7.79/1.50      ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top
% 7.79/1.50      | v1_relat_1(k9_relat_1(k2_relat_1(k1_xboole_0),k1_xboole_0)) = iProver_top
% 7.79/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.79/1.50      inference(light_normalisation,[status(thm)],[c_20679,c_15065,c_19957]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_25,negated_conjecture,
% 7.79/1.50      ( v1_funct_1(sK10) ),
% 7.79/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_23,negated_conjecture,
% 7.79/1.50      ( v2_funct_1(sK10) ),
% 7.79/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_22,negated_conjecture,
% 7.79/1.50      ( ~ r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,sK9)) ),
% 7.79/1.50      inference(cnf_transformation,[],[f84]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_0,plain,
% 7.79/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.79/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1054,plain,
% 7.79/1.50      ( ~ r1_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8))
% 7.79/1.50      | r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,sK9)) ),
% 7.79/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_2,plain,
% 7.79/1.50      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(k3_xboole_0(X0,X1),X1) ),
% 7.79/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1183,plain,
% 7.79/1.50      ( r1_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8))
% 7.79/1.50      | ~ r1_xboole_0(k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)),k9_relat_1(sK10,sK8)) ),
% 7.79/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_377,plain,( X0 = X0 ),theory(equality) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1228,plain,
% 7.79/1.50      ( k9_relat_1(sK10,sK8) = k9_relat_1(sK10,sK8) ),
% 7.79/1.50      inference(instantiation,[status(thm)],[c_377]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1418,plain,
% 7.79/1.50      ( r1_xboole_0(k9_relat_1(sK10,sK8),k1_xboole_0) ),
% 7.79/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_379,plain,
% 7.79/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.79/1.50      theory(equality) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1317,plain,
% 7.79/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.79/1.50      | r1_xboole_0(k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)),k9_relat_1(sK10,sK8))
% 7.79/1.50      | k9_relat_1(sK10,sK8) != X1
% 7.79/1.50      | k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)) != X0 ),
% 7.79/1.50      inference(instantiation,[status(thm)],[c_379]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1580,plain,
% 7.79/1.50      ( ~ r1_xboole_0(X0,k9_relat_1(sK10,sK8))
% 7.79/1.50      | r1_xboole_0(k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)),k9_relat_1(sK10,sK8))
% 7.79/1.50      | k9_relat_1(sK10,sK8) != k9_relat_1(sK10,sK8)
% 7.79/1.50      | k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)) != X0 ),
% 7.79/1.50      inference(instantiation,[status(thm)],[c_1317]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_2264,plain,
% 7.79/1.50      ( ~ r1_xboole_0(k9_relat_1(sK10,k3_xboole_0(sK9,sK8)),k9_relat_1(sK10,sK8))
% 7.79/1.50      | r1_xboole_0(k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)),k9_relat_1(sK10,sK8))
% 7.79/1.50      | k9_relat_1(sK10,sK8) != k9_relat_1(sK10,sK8)
% 7.79/1.50      | k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)) != k9_relat_1(sK10,k3_xboole_0(sK9,sK8)) ),
% 7.79/1.50      inference(instantiation,[status(thm)],[c_1580]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_21,plain,
% 7.79/1.50      ( ~ v1_funct_1(X0)
% 7.79/1.50      | ~ v2_funct_1(X0)
% 7.79/1.50      | ~ v1_relat_1(X0)
% 7.79/1.50      | k3_xboole_0(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 7.79/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1141,plain,
% 7.79/1.50      ( ~ v1_funct_1(sK10)
% 7.79/1.50      | ~ v2_funct_1(sK10)
% 7.79/1.50      | ~ v1_relat_1(sK10)
% 7.79/1.50      | k3_xboole_0(k9_relat_1(sK10,X0),k9_relat_1(sK10,X1)) = k9_relat_1(sK10,k3_xboole_0(X0,X1)) ),
% 7.79/1.50      inference(instantiation,[status(thm)],[c_21]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_2265,plain,
% 7.79/1.50      ( ~ v1_funct_1(sK10)
% 7.79/1.50      | ~ v2_funct_1(sK10)
% 7.79/1.50      | ~ v1_relat_1(sK10)
% 7.79/1.50      | k3_xboole_0(k9_relat_1(sK10,sK9),k9_relat_1(sK10,sK8)) = k9_relat_1(sK10,k3_xboole_0(sK9,sK8)) ),
% 7.79/1.50      inference(instantiation,[status(thm)],[c_1141]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1843,plain,
% 7.79/1.50      ( r1_xboole_0(X0,k9_relat_1(sK10,sK8))
% 7.79/1.50      | ~ r1_xboole_0(k9_relat_1(sK10,sK8),X0) ),
% 7.79/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_3349,plain,
% 7.79/1.50      ( r1_xboole_0(k9_relat_1(sK10,k3_xboole_0(sK9,sK8)),k9_relat_1(sK10,sK8))
% 7.79/1.50      | ~ r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,k3_xboole_0(sK9,sK8))) ),
% 7.79/1.50      inference(instantiation,[status(thm)],[c_1843]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1423,plain,
% 7.79/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.79/1.50      | r1_xboole_0(k9_relat_1(sK10,sK8),X2)
% 7.79/1.50      | X2 != X1
% 7.79/1.50      | k9_relat_1(sK10,sK8) != X0 ),
% 7.79/1.50      inference(instantiation,[status(thm)],[c_379]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1999,plain,
% 7.79/1.50      ( ~ r1_xboole_0(k9_relat_1(sK10,sK8),X0)
% 7.79/1.50      | r1_xboole_0(k9_relat_1(sK10,sK8),X1)
% 7.79/1.50      | X1 != X0
% 7.79/1.50      | k9_relat_1(sK10,sK8) != k9_relat_1(sK10,sK8) ),
% 7.79/1.50      inference(instantiation,[status(thm)],[c_1423]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_3743,plain,
% 7.79/1.50      ( ~ r1_xboole_0(k9_relat_1(sK10,sK8),X0)
% 7.79/1.50      | r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,k3_xboole_0(sK9,sK8)))
% 7.79/1.50      | k9_relat_1(sK10,k3_xboole_0(sK9,sK8)) != X0
% 7.79/1.50      | k9_relat_1(sK10,sK8) != k9_relat_1(sK10,sK8) ),
% 7.79/1.50      inference(instantiation,[status(thm)],[c_1999]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_3745,plain,
% 7.79/1.50      ( r1_xboole_0(k9_relat_1(sK10,sK8),k9_relat_1(sK10,k3_xboole_0(sK9,sK8)))
% 7.79/1.50      | ~ r1_xboole_0(k9_relat_1(sK10,sK8),k1_xboole_0)
% 7.79/1.50      | k9_relat_1(sK10,k3_xboole_0(sK9,sK8)) != k1_xboole_0
% 7.79/1.50      | k9_relat_1(sK10,sK8) != k9_relat_1(sK10,sK8) ),
% 7.79/1.50      inference(instantiation,[status(thm)],[c_3743]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_11,plain,
% 7.79/1.50      ( ~ v1_relat_1(X0)
% 7.79/1.50      | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 7.79/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_859,plain,
% 7.79/1.50      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2))
% 7.79/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1667,plain,
% 7.79/1.50      ( k7_relat_1(sK10,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(sK10,X0),X1) ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_845,c_859]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_24,negated_conjecture,
% 7.79/1.50      ( r1_xboole_0(sK8,sK9) ),
% 7.79/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_847,plain,
% 7.79/1.50      ( r1_xboole_0(sK8,sK9) = iProver_top ),
% 7.79/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_870,plain,
% 7.79/1.50      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 7.79/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_1467,plain,
% 7.79/1.50      ( r1_xboole_0(sK9,sK8) = iProver_top ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_847,c_870]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_15,plain,
% 7.79/1.50      ( ~ r1_xboole_0(X0,X1)
% 7.79/1.50      | ~ v1_relat_1(X2)
% 7.79/1.50      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 7.79/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_855,plain,
% 7.79/1.50      ( k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
% 7.79/1.50      | r1_xboole_0(X1,X2) != iProver_top
% 7.79/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_2480,plain,
% 7.79/1.50      ( k7_relat_1(k7_relat_1(X0,sK9),sK8) = k1_xboole_0
% 7.79/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_1467,c_855]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_4094,plain,
% 7.79/1.50      ( k7_relat_1(k7_relat_1(sK10,sK9),sK8) = k1_xboole_0 ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_845,c_2480]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_4310,plain,
% 7.79/1.50      ( k7_relat_1(sK10,k3_xboole_0(sK9,sK8)) = k1_xboole_0 ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_1667,c_4094]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_17,plain,
% 7.79/1.50      ( r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
% 7.79/1.50      | ~ v1_relat_1(X0)
% 7.79/1.50      | k1_xboole_0 = X0 ),
% 7.79/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_853,plain,
% 7.79/1.50      ( k1_xboole_0 = X0
% 7.79/1.50      | r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0) = iProver_top
% 7.79/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.79/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_5173,plain,
% 7.79/1.50      ( k9_relat_1(sK10,X0) = k1_xboole_0
% 7.79/1.50      | r2_hidden(sK5(k7_relat_1(sK10,X0)),k1_relat_1(k7_relat_1(sK10,X0))) = iProver_top
% 7.79/1.50      | v1_relat_1(k9_relat_1(sK10,X0)) != iProver_top
% 7.79/1.50      | v1_relat_1(k7_relat_1(sK10,X0)) != iProver_top ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_853,c_3029]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_5206,plain,
% 7.79/1.50      ( k9_relat_1(sK10,X0) = k1_xboole_0
% 7.79/1.50      | r2_hidden(sK5(k7_relat_1(sK10,X0)),k1_relat_1(k7_relat_1(sK10,X0))) = iProver_top
% 7.79/1.50      | v1_relat_1(k7_relat_1(sK10,X0)) != iProver_top ),
% 7.79/1.50      inference(backward_subsumption_resolution,[status(thm)],[c_5171,c_5173]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_19012,plain,
% 7.79/1.50      ( k9_relat_1(sK10,k3_xboole_0(sK9,sK8)) = k1_xboole_0
% 7.79/1.50      | r2_hidden(sK5(k1_xboole_0),k1_relat_1(k1_xboole_0)) = iProver_top
% 7.79/1.50      | v1_relat_1(k7_relat_1(sK10,k3_xboole_0(sK9,sK8))) != iProver_top ),
% 7.79/1.50      inference(superposition,[status(thm)],[c_4310,c_5206]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_19025,plain,
% 7.79/1.50      ( k9_relat_1(sK10,k3_xboole_0(sK9,sK8)) = k1_xboole_0
% 7.79/1.50      | r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top
% 7.79/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.79/1.50      inference(light_normalisation,[status(thm)],[c_19012,c_4310,c_15065]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_28760,plain,
% 7.79/1.50      ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.79/1.50      inference(global_propositional_subsumption,
% 7.79/1.50                [status(thm)],
% 7.79/1.50                [c_20693,c_26,c_25,c_23,c_22,c_1054,c_1183,c_1228,c_1418,
% 7.79/1.50                 c_2264,c_2265,c_2666,c_3349,c_3745,c_19025]) ).
% 7.79/1.50  
% 7.79/1.50  cnf(c_28765,plain,
% 7.79/1.50      ( $false ),
% 7.79/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_28760,c_1588]) ).
% 7.79/1.50  
% 7.79/1.50  
% 7.79/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.79/1.50  
% 7.79/1.50  ------                               Statistics
% 7.79/1.50  
% 7.79/1.50  ------ Selected
% 7.79/1.50  
% 7.79/1.50  total_time:                             0.856
% 7.79/1.50  
%------------------------------------------------------------------------------
