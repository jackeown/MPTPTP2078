%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:04 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 168 expanded)
%              Number of leaves         :   11 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  241 ( 815 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1135,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1118,f1097])).

fof(f1097,plain,(
    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f74,f234])).

fof(f234,plain,(
    ! [X4,X3] :
      ( r2_hidden(k4_tarski(X3,X4),k8_relat_1(sK1,sK2))
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f233,f51])).

fof(f51,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f30,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

fof(f233,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(sK0,sK2))
      | r2_hidden(k4_tarski(X3,X4),k8_relat_1(sK1,sK2))
      | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ) ),
    inference(subsumption_resolution,[],[f228,f51])).

fof(f228,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(sK0,sK2))
      | r2_hidden(k4_tarski(X3,X4),k8_relat_1(sK1,sK2))
      | ~ v1_relat_1(k8_relat_1(sK1,sK2)) ) ),
    inference(superposition,[],[f49,f155])).

fof(f155,plain,(
    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2)) ),
    inference(superposition,[],[f52,f72])).

fof(f72,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f33,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f33,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X0,X1] : k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2) ),
    inference(unit_resulting_resolution,[],[f30,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).

fof(f49,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X5,X6),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK7(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
                    & r2_hidden(sK7(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
          | ~ r2_hidden(sK7(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
            & r2_hidden(sK7(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(f74,plain,(
    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f34,f51,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f34,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f1118,plain,(
    ~ r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f51,f70,f75,f35])).

fof(f35,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(X4,X5),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    ~ r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f34,f51,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    ! [X0] : r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(X0,sK3)) ),
    inference(unit_resulting_resolution,[],[f30,f31,f32,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

fof(f32,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (29996)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (30003)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (30004)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (29995)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (29997)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (30005)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (29993)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (29989)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (29991)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (29994)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (29990)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (30008)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (29990)Refutation not found, incomplete strategy% (29990)------------------------------
% 0.21/0.51  % (29990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29990)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29990)Memory used [KB]: 10490
% 0.21/0.51  % (29990)Time elapsed: 0.100 s
% 0.21/0.51  % (29990)------------------------------
% 0.21/0.51  % (29990)------------------------------
% 0.21/0.51  % (30009)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (29992)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (30009)Refutation not found, incomplete strategy% (30009)------------------------------
% 0.21/0.51  % (30009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30009)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30009)Memory used [KB]: 10490
% 0.21/0.51  % (30009)Time elapsed: 0.106 s
% 0.21/0.51  % (30009)------------------------------
% 0.21/0.51  % (30009)------------------------------
% 0.21/0.51  % (30007)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (30002)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (30001)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (29999)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (30000)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (29998)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  % (30006)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.57/0.55  % (30004)Refutation found. Thanks to Tanya!
% 1.57/0.55  % SZS status Theorem for theBenchmark
% 1.57/0.55  % SZS output start Proof for theBenchmark
% 1.57/0.55  fof(f1135,plain,(
% 1.57/0.55    $false),
% 1.57/0.55    inference(subsumption_resolution,[],[f1118,f1097])).
% 1.57/0.55  fof(f1097,plain,(
% 1.57/0.55    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2))),
% 1.57/0.55    inference(unit_resulting_resolution,[],[f74,f234])).
% 1.57/0.55  fof(f234,plain,(
% 1.57/0.55    ( ! [X4,X3] : (r2_hidden(k4_tarski(X3,X4),k8_relat_1(sK1,sK2)) | ~r2_hidden(k4_tarski(X3,X4),k8_relat_1(sK0,sK2))) )),
% 1.57/0.55    inference(subsumption_resolution,[],[f233,f51])).
% 1.57/0.55  fof(f51,plain,(
% 1.57/0.55    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK2))) )),
% 1.57/0.55    inference(unit_resulting_resolution,[],[f30,f38])).
% 1.57/0.55  fof(f38,plain,(
% 1.57/0.55    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 1.57/0.55    inference(cnf_transformation,[],[f12])).
% 1.57/0.56  fof(f12,plain,(
% 1.57/0.56    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 1.57/0.56    inference(ennf_transformation,[],[f4])).
% 1.57/0.56  fof(f4,axiom,(
% 1.57/0.56    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 1.57/0.56  fof(f30,plain,(
% 1.57/0.56    v1_relat_1(sK2)),
% 1.57/0.56    inference(cnf_transformation,[],[f20])).
% 1.57/0.56  fof(f20,plain,(
% 1.57/0.56    (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 1.57/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f19,f18])).
% 1.57/0.56  fof(f18,plain,(
% 1.57/0.56    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f19,plain,(
% 1.57/0.56    ? [X3] : (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,X3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f10,plain,(
% 1.57/0.56    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.57/0.56    inference(flattening,[],[f9])).
% 1.57/0.56  fof(f9,plain,(
% 1.57/0.56    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 1.57/0.56    inference(ennf_transformation,[],[f8])).
% 1.57/0.56  fof(f8,negated_conjecture,(
% 1.57/0.56    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 1.57/0.56    inference(negated_conjecture,[],[f7])).
% 1.57/0.56  fof(f7,conjecture,(
% 1.57/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)))))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).
% 1.57/0.56  fof(f233,plain,(
% 1.57/0.56    ( ! [X4,X3] : (~r2_hidden(k4_tarski(X3,X4),k8_relat_1(sK0,sK2)) | r2_hidden(k4_tarski(X3,X4),k8_relat_1(sK1,sK2)) | ~v1_relat_1(k8_relat_1(sK1,sK2))) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f228,f51])).
% 1.57/0.56  fof(f228,plain,(
% 1.57/0.56    ( ! [X4,X3] : (~v1_relat_1(k8_relat_1(sK0,sK2)) | ~r2_hidden(k4_tarski(X3,X4),k8_relat_1(sK0,sK2)) | r2_hidden(k4_tarski(X3,X4),k8_relat_1(sK1,sK2)) | ~v1_relat_1(k8_relat_1(sK1,sK2))) )),
% 1.57/0.56    inference(superposition,[],[f49,f155])).
% 1.57/0.56  fof(f155,plain,(
% 1.57/0.56    k8_relat_1(sK0,sK2) = k8_relat_1(sK0,k8_relat_1(sK1,sK2))),
% 1.57/0.56    inference(superposition,[],[f52,f72])).
% 1.57/0.56  fof(f72,plain,(
% 1.57/0.56    sK0 = k3_xboole_0(sK0,sK1)),
% 1.57/0.56    inference(unit_resulting_resolution,[],[f33,f46])).
% 1.57/0.56  fof(f46,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.57/0.56    inference(cnf_transformation,[],[f16])).
% 1.57/0.56  fof(f16,plain,(
% 1.57/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.57/0.56    inference(ennf_transformation,[],[f1])).
% 1.57/0.56  fof(f1,axiom,(
% 1.57/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.57/0.56  fof(f33,plain,(
% 1.57/0.56    r1_tarski(sK0,sK1)),
% 1.57/0.56    inference(cnf_transformation,[],[f20])).
% 1.57/0.56  fof(f52,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,sK2)) = k8_relat_1(k3_xboole_0(X0,X1),sK2)) )),
% 1.57/0.56    inference(unit_resulting_resolution,[],[f30,f47])).
% 1.57/0.56  fof(f47,plain,(
% 1.57/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f17])).
% 1.57/0.56  fof(f17,plain,(
% 1.57/0.56    ! [X0,X1,X2] : (k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.57/0.56    inference(ennf_transformation,[],[f5])).
% 1.57/0.56  fof(f5,axiom,(
% 1.57/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => k8_relat_1(X0,k8_relat_1(X1,X2)) = k8_relat_1(k3_xboole_0(X0,X1),X2))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_relat_1)).
% 1.57/0.56  fof(f49,plain,(
% 1.57/0.56    ( ! [X6,X0,X5,X1] : (~v1_relat_1(k8_relat_1(X0,X1)) | ~r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1)) | r2_hidden(k4_tarski(X5,X6),X1) | ~v1_relat_1(X1)) )),
% 1.57/0.56    inference(equality_resolution,[],[f41])).
% 1.57/0.56  fof(f41,plain,(
% 1.57/0.56    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k8_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f29])).
% 1.57/0.56  fof(f29,plain,(
% 1.57/0.56    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.57/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f27,f28])).
% 1.57/0.56  fof(f28,plain,(
% 1.57/0.56    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1) | ~r2_hidden(sK7(X0,X1,X2),X0) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2))))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f27,plain,(
% 1.57/0.56    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X1) | ~r2_hidden(X6,X0)) & ((r2_hidden(k4_tarski(X5,X6),X1) & r2_hidden(X6,X0)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.57/0.56    inference(rectify,[],[f26])).
% 1.57/0.56  fof(f26,plain,(
% 1.57/0.56    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.57/0.56    inference(flattening,[],[f25])).
% 1.57/0.56  fof(f25,plain,(
% 1.57/0.56    ! [X0,X1] : (! [X2] : (((k8_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(X4,X0))) & ((r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k8_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.57/0.56    inference(nnf_transformation,[],[f15])).
% 1.57/0.56  fof(f15,plain,(
% 1.57/0.56    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.57/0.56    inference(ennf_transformation,[],[f2])).
% 1.57/0.56  fof(f2,axiom,(
% 1.57/0.56    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).
% 1.57/0.56  fof(f74,plain,(
% 1.57/0.56    r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK0,sK2))),
% 1.57/0.56    inference(unit_resulting_resolution,[],[f34,f51,f36])).
% 1.57/0.56  fof(f36,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f24])).
% 1.57/0.56  fof(f24,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f22,f23])).
% 1.57/0.56  fof(f23,plain,(
% 1.57/0.56    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)))),
% 1.57/0.56    introduced(choice_axiom,[])).
% 1.57/0.56  fof(f22,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(rectify,[],[f21])).
% 1.57/0.56  fof(f21,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(nnf_transformation,[],[f11])).
% 1.57/0.56  fof(f11,plain,(
% 1.57/0.56    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(ennf_transformation,[],[f3])).
% 1.57/0.56  fof(f3,axiom,(
% 1.57/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 1.57/0.56  fof(f34,plain,(
% 1.57/0.56    ~r1_tarski(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),
% 1.57/0.56    inference(cnf_transformation,[],[f20])).
% 1.57/0.56  fof(f1118,plain,(
% 1.57/0.56    ~r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK2))),
% 1.57/0.56    inference(unit_resulting_resolution,[],[f51,f70,f75,f35])).
% 1.57/0.56  fof(f35,plain,(
% 1.57/0.56    ( ! [X4,X0,X5,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X0,X1) | r2_hidden(k4_tarski(X4,X5),X1)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f24])).
% 1.57/0.56  fof(f75,plain,(
% 1.57/0.56    ~r2_hidden(k4_tarski(sK4(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3)),sK5(k8_relat_1(sK0,sK2),k8_relat_1(sK1,sK3))),k8_relat_1(sK1,sK3))),
% 1.57/0.56    inference(unit_resulting_resolution,[],[f34,f51,f37])).
% 1.57/0.56  fof(f37,plain,(
% 1.57/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) | r1_tarski(X0,X1)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f24])).
% 1.57/0.56  fof(f70,plain,(
% 1.57/0.56    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK2),k8_relat_1(X0,sK3))) )),
% 1.57/0.56    inference(unit_resulting_resolution,[],[f30,f31,f32,f39])).
% 1.57/0.56  fof(f39,plain,(
% 1.57/0.56    ( ! [X2,X0,X1] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.57/0.56    inference(cnf_transformation,[],[f14])).
% 1.57/0.56  fof(f14,plain,(
% 1.57/0.56    ! [X0,X1] : (! [X2] : (r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.57/0.56    inference(flattening,[],[f13])).
% 1.57/0.56  fof(f13,plain,(
% 1.57/0.56    ! [X0,X1] : (! [X2] : ((r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.57/0.56    inference(ennf_transformation,[],[f6])).
% 1.57/0.56  fof(f6,axiom,(
% 1.57/0.56    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).
% 1.57/0.56  fof(f32,plain,(
% 1.57/0.56    r1_tarski(sK2,sK3)),
% 1.57/0.56    inference(cnf_transformation,[],[f20])).
% 1.57/0.56  fof(f31,plain,(
% 1.57/0.56    v1_relat_1(sK3)),
% 1.57/0.56    inference(cnf_transformation,[],[f20])).
% 1.57/0.56  % SZS output end Proof for theBenchmark
% 1.57/0.56  % (30004)------------------------------
% 1.57/0.56  % (30004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (30004)Termination reason: Refutation
% 1.57/0.56  
% 1.57/0.56  % (30004)Memory used [KB]: 7419
% 1.57/0.56  % (30004)Time elapsed: 0.131 s
% 1.57/0.56  % (30004)------------------------------
% 1.57/0.56  % (30004)------------------------------
% 1.57/0.56  % (29988)Success in time 0.202 s
%------------------------------------------------------------------------------
