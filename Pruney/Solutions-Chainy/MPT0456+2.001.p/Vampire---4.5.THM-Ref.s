%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:23 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   51 (  76 expanded)
%              Number of leaves         :   14 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  243 ( 360 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(subsumption_resolution,[],[f95,f32])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,X1)),k1_relat_1(sK0))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,X1)),k1_relat_1(sK0))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f95,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f94,f33])).

fof(f33,plain,(
    ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f94,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,X2)),k1_relat_1(sK0))
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(k5_relat_1(sK0,X2)),k1_relat_1(sK0))
      | ~ v1_relat_1(X2)
      | r1_tarski(k1_relat_1(k5_relat_1(sK0,X2)),k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f86,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f15])).

% (4633)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f86,plain,(
    ! [X8,X7] :
      ( r2_hidden(sK2(k1_relat_1(k5_relat_1(sK0,X7)),X8),k1_relat_1(sK0))
      | r1_tarski(k1_relat_1(k5_relat_1(sK0,X7)),X8)
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f81,f48])).

fof(f48,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f23,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(k1_relat_1(k5_relat_1(sK0,X0)),X1),sK9(sK0,X0,sK2(k1_relat_1(k5_relat_1(sK0,X0)),X1),sK5(k5_relat_1(sK0,X0),sK2(k1_relat_1(k5_relat_1(sK0,X0)),X1)))),sK0)
      | ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(k5_relat_1(sK0,X0)),X1) ) ),
    inference(resolution,[],[f72,f31])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK2(k1_relat_1(k5_relat_1(X0,X1)),X2),sK9(X0,X1,sK2(k1_relat_1(k5_relat_1(X0,X1)),X2),sK5(k5_relat_1(X0,X1),sK2(k1_relat_1(k5_relat_1(X0,X1)),X2)))),X0)
      | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),X2) ) ),
    inference(resolution,[],[f62,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(k1_relat_1(X0),X1),sK5(X0,sK2(k1_relat_1(X0),X1))),X0)
      | r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0,X8,X7,X1] :
      ( ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f52,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f52,plain,(
    ! [X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X8,X7,X1] :
      ( r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0)
      | ~ r2_hidden(k4_tarski(X7,X8),X2)
      | k5_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK7(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X2),sK7(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK8(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f26,f29,f28,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK7(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK7(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK6(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK7(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK6(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK8(X0,X1,X2),sK7(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK8(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:19:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.25/0.56  % (4642)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.56/0.56  % (4634)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.56/0.56  % (4626)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.56/0.57  % (4636)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.56/0.57  % (4623)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.56/0.57  % (4624)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.56/0.57  % (4622)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.56/0.57  % (4628)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.56/0.58  % (4620)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.56/0.58  % (4631)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.58  % (4619)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.56/0.59  % (4636)Refutation found. Thanks to Tanya!
% 1.56/0.59  % SZS status Theorem for theBenchmark
% 1.56/0.59  % SZS output start Proof for theBenchmark
% 1.56/0.59  fof(f98,plain,(
% 1.56/0.59    $false),
% 1.56/0.59    inference(subsumption_resolution,[],[f95,f32])).
% 1.56/0.59  fof(f32,plain,(
% 1.56/0.59    v1_relat_1(sK1)),
% 1.56/0.59    inference(cnf_transformation,[],[f14])).
% 1.56/0.59  fof(f14,plain,(
% 1.56/0.59    (~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 1.56/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).
% 1.56/0.59  fof(f12,plain,(
% 1.56/0.59    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k1_relat_1(k5_relat_1(sK0,X1)),k1_relat_1(sK0)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 1.56/0.59    introduced(choice_axiom,[])).
% 1.56/0.59  fof(f13,plain,(
% 1.56/0.59    ? [X1] : (~r1_tarski(k1_relat_1(k5_relat_1(sK0,X1)),k1_relat_1(sK0)) & v1_relat_1(X1)) => (~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0)) & v1_relat_1(sK1))),
% 1.56/0.59    introduced(choice_axiom,[])).
% 1.56/0.59  fof(f7,plain,(
% 1.56/0.59    ? [X0] : (? [X1] : (~r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.56/0.59    inference(ennf_transformation,[],[f6])).
% 1.56/0.59  fof(f6,negated_conjecture,(
% 1.56/0.59    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.56/0.59    inference(negated_conjecture,[],[f5])).
% 1.56/0.59  fof(f5,conjecture,(
% 1.56/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 1.56/0.59  fof(f95,plain,(
% 1.56/0.59    ~v1_relat_1(sK1)),
% 1.56/0.59    inference(resolution,[],[f94,f33])).
% 1.56/0.59  fof(f33,plain,(
% 1.56/0.59    ~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k1_relat_1(sK0))),
% 1.56/0.59    inference(cnf_transformation,[],[f14])).
% 1.56/0.59  fof(f94,plain,(
% 1.56/0.59    ( ! [X2] : (r1_tarski(k1_relat_1(k5_relat_1(sK0,X2)),k1_relat_1(sK0)) | ~v1_relat_1(X2)) )),
% 1.56/0.59    inference(duplicate_literal_removal,[],[f92])).
% 1.56/0.59  fof(f92,plain,(
% 1.56/0.59    ( ! [X2] : (r1_tarski(k1_relat_1(k5_relat_1(sK0,X2)),k1_relat_1(sK0)) | ~v1_relat_1(X2) | r1_tarski(k1_relat_1(k5_relat_1(sK0,X2)),k1_relat_1(sK0))) )),
% 1.56/0.59    inference(resolution,[],[f86,f36])).
% 1.56/0.59  fof(f36,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f18])).
% 1.56/0.59  fof(f18,plain,(
% 1.56/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).
% 1.56/0.59  fof(f17,plain,(
% 1.56/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.56/0.59    introduced(choice_axiom,[])).
% 1.56/0.59  fof(f16,plain,(
% 1.56/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.59    inference(rectify,[],[f15])).
% 1.56/0.59  % (4633)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.56/0.59  fof(f15,plain,(
% 1.56/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.59    inference(nnf_transformation,[],[f8])).
% 1.56/0.59  fof(f8,plain,(
% 1.56/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.56/0.59    inference(ennf_transformation,[],[f1])).
% 1.56/0.59  fof(f1,axiom,(
% 1.56/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.56/0.59  fof(f86,plain,(
% 1.56/0.59    ( ! [X8,X7] : (r2_hidden(sK2(k1_relat_1(k5_relat_1(sK0,X7)),X8),k1_relat_1(sK0)) | r1_tarski(k1_relat_1(k5_relat_1(sK0,X7)),X8) | ~v1_relat_1(X7)) )),
% 1.56/0.59    inference(resolution,[],[f81,f48])).
% 1.56/0.59  fof(f48,plain,(
% 1.56/0.59    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 1.56/0.59    inference(equality_resolution,[],[f38])).
% 1.56/0.59  fof(f38,plain,(
% 1.56/0.59    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.56/0.59    inference(cnf_transformation,[],[f24])).
% 1.56/0.59  fof(f24,plain,(
% 1.56/0.59    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.56/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f20,f23,f22,f21])).
% 1.56/0.59  fof(f21,plain,(
% 1.56/0.59    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.56/0.59    introduced(choice_axiom,[])).
% 1.56/0.59  fof(f22,plain,(
% 1.56/0.59    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 1.56/0.59    introduced(choice_axiom,[])).
% 1.56/0.59  fof(f23,plain,(
% 1.56/0.59    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 1.56/0.59    introduced(choice_axiom,[])).
% 1.56/0.59  fof(f20,plain,(
% 1.56/0.59    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.56/0.59    inference(rectify,[],[f19])).
% 1.56/0.59  fof(f19,plain,(
% 1.56/0.59    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.56/0.59    inference(nnf_transformation,[],[f2])).
% 1.56/0.59  fof(f2,axiom,(
% 1.56/0.59    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.56/0.59  fof(f81,plain,(
% 1.56/0.59    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(k1_relat_1(k5_relat_1(sK0,X0)),X1),sK9(sK0,X0,sK2(k1_relat_1(k5_relat_1(sK0,X0)),X1),sK5(k5_relat_1(sK0,X0),sK2(k1_relat_1(k5_relat_1(sK0,X0)),X1)))),sK0) | ~v1_relat_1(X0) | r1_tarski(k1_relat_1(k5_relat_1(sK0,X0)),X1)) )),
% 1.56/0.59    inference(resolution,[],[f72,f31])).
% 1.56/0.59  fof(f31,plain,(
% 1.56/0.59    v1_relat_1(sK0)),
% 1.56/0.59    inference(cnf_transformation,[],[f14])).
% 1.56/0.59  fof(f72,plain,(
% 1.56/0.59    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK2(k1_relat_1(k5_relat_1(X0,X1)),X2),sK9(X0,X1,sK2(k1_relat_1(k5_relat_1(X0,X1)),X2),sK5(k5_relat_1(X0,X1),sK2(k1_relat_1(k5_relat_1(X0,X1)),X2)))),X0) | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),X2)) )),
% 1.56/0.59    inference(resolution,[],[f62,f66])).
% 1.56/0.59  fof(f66,plain,(
% 1.56/0.59    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(k1_relat_1(X0),X1),sK5(X0,sK2(k1_relat_1(X0),X1))),X0) | r1_tarski(k1_relat_1(X0),X1)) )),
% 1.56/0.59    inference(resolution,[],[f49,f35])).
% 1.56/0.59  fof(f35,plain,(
% 1.56/0.59    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f18])).
% 1.56/0.59  fof(f49,plain,(
% 1.56/0.59    ( ! [X0,X5] : (~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)) )),
% 1.56/0.59    inference(equality_resolution,[],[f37])).
% 1.56/0.59  fof(f37,plain,(
% 1.56/0.59    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.56/0.59    inference(cnf_transformation,[],[f24])).
% 1.56/0.59  fof(f62,plain,(
% 1.56/0.59    ( ! [X0,X8,X7,X1] : (~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.56/0.59    inference(subsumption_resolution,[],[f52,f41])).
% 1.56/0.59  fof(f41,plain,(
% 1.56/0.59    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f10])).
% 1.56/0.59  fof(f10,plain,(
% 1.56/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.56/0.59    inference(flattening,[],[f9])).
% 1.56/0.59  fof(f9,plain,(
% 1.56/0.59    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.56/0.59    inference(ennf_transformation,[],[f4])).
% 1.56/0.59  fof(f4,axiom,(
% 1.56/0.59    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.56/0.59  fof(f52,plain,(
% 1.56/0.59    ( ! [X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),k5_relat_1(X0,X1)) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.56/0.59    inference(equality_resolution,[],[f42])).
% 1.56/0.59  fof(f42,plain,(
% 1.56/0.59    ( ! [X2,X0,X8,X7,X1] : (r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0) | ~r2_hidden(k4_tarski(X7,X8),X2) | k5_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f30])).
% 1.56/0.59  fof(f30,plain,(
% 1.56/0.59    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK7(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK8(X0,X1,X2),sK7(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK8(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.56/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f26,f29,f28,f27])).
% 1.56/0.59  fof(f27,plain,(
% 1.56/0.59    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK7(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK7(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2))))),
% 1.56/0.59    introduced(choice_axiom,[])).
% 1.56/0.59  fof(f28,plain,(
% 1.56/0.59    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK7(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK8(X0,X1,X2),sK7(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK8(X0,X1,X2)),X0)))),
% 1.56/0.59    introduced(choice_axiom,[])).
% 1.56/0.59  fof(f29,plain,(
% 1.56/0.59    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK9(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK9(X0,X1,X7,X8)),X0)))),
% 1.56/0.59    introduced(choice_axiom,[])).
% 1.56/0.59  fof(f26,plain,(
% 1.56/0.59    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.56/0.59    inference(rectify,[],[f25])).
% 1.56/0.59  fof(f25,plain,(
% 1.56/0.59    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.56/0.59    inference(nnf_transformation,[],[f11])).
% 1.56/0.59  fof(f11,plain,(
% 1.56/0.59    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.56/0.59    inference(ennf_transformation,[],[f3])).
% 1.56/0.59  fof(f3,axiom,(
% 1.56/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 1.56/0.59  % SZS output end Proof for theBenchmark
% 1.56/0.59  % (4636)------------------------------
% 1.56/0.59  % (4636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.59  % (4636)Termination reason: Refutation
% 1.56/0.59  
% 1.56/0.59  % (4636)Memory used [KB]: 10746
% 1.56/0.59  % (4636)Time elapsed: 0.145 s
% 1.56/0.59  % (4636)------------------------------
% 1.56/0.59  % (4636)------------------------------
% 1.56/0.59  % (4621)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.56/0.59  % (4639)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.56/0.59  % (4621)Refutation not found, incomplete strategy% (4621)------------------------------
% 1.56/0.59  % (4621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.59  % (4621)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.59  
% 1.56/0.59  % (4621)Memory used [KB]: 10618
% 1.56/0.59  % (4621)Time elapsed: 0.163 s
% 1.56/0.59  % (4621)------------------------------
% 1.56/0.59  % (4621)------------------------------
% 1.56/0.59  % (4635)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.56/0.59  % (4618)Success in time 0.227 s
%------------------------------------------------------------------------------
