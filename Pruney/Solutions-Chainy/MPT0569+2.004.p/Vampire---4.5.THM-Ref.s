%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  109 (1545 expanded)
%              Number of leaves         :   18 ( 445 expanded)
%              Depth                    :   27
%              Number of atoms          :  430 (8179 expanded)
%              Number of equality atoms :   54 (1401 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2986,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2984,f2704])).

fof(f2704,plain,(
    r2_hidden(sK5(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f2702,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f2702,plain,(
    ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f2701])).

fof(f2701,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(backward_demodulation,[],[f48,f2700])).

fof(f2700,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f2686])).

fof(f2686,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(resolution,[],[f2616,f361])).

fof(f361,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f348,f349])).

fof(f349,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f51,f348])).

fof(f51,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f348,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k10_relat_1(sK1,k1_xboole_0) = X0 ) ),
    inference(duplicate_literal_removal,[],[f339])).

fof(f339,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k10_relat_1(sK1,k1_xboole_0) = X0
      | k10_relat_1(sK1,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f285,f284])).

fof(f284,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,k1_xboole_0,X0),X0)
      | k10_relat_1(sK1,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f283,f51])).

fof(f283,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | k10_relat_1(sK1,X0) = X1
      | r2_hidden(sK2(sK1,X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK1,X0) = X1
      | ~ r1_xboole_0(X0,X0)
      | r2_hidden(sK2(sK1,X0,X1),X1)
      | r2_hidden(sK2(sK1,X0,X1),X1)
      | k10_relat_1(sK1,X0) = X1 ) ),
    inference(resolution,[],[f128,f83])).

fof(f83,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(sK1,X2,X3),X2)
      | r2_hidden(sK2(sK1,X2,X3),X3)
      | k10_relat_1(sK1,X2) = X3 ) ),
    inference(resolution,[],[f46,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f46,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 != k10_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 = k10_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 != k10_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 = k10_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(sK1,X0,X1),X2)
      | k10_relat_1(sK1,X0) = X1
      | ~ r1_xboole_0(X2,X0)
      | r2_hidden(sK2(sK1,X0,X1),X1) ) ),
    inference(resolution,[],[f83,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f285,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(sK1,k1_xboole_0,X0),X1)
      | ~ r1_xboole_0(X1,X0)
      | k10_relat_1(sK1,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f284,f61])).

fof(f2616,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,k10_relat_1(sK1,sK0))
      | k1_xboole_0 = k10_relat_1(sK1,sK0) ) ),
    inference(resolution,[],[f2605,f47])).

fof(f47,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f2605,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(sK1),X0)
      | r1_xboole_0(X1,k10_relat_1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f2593,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2593,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(sK1),X0)
      | r1_xboole_0(X1,k10_relat_1(sK1,X0))
      | ~ r2_hidden(sK5(X1,k10_relat_1(sK1,X0)),k10_relat_1(sK1,X0)) ) ),
    inference(resolution,[],[f160,f254])).

fof(f254,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1,sK1),k2_relat_1(sK1))
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f253,f112])).

fof(f112,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,k10_relat_1(sK1,X4))
      | r2_hidden(X3,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f88,f78])).

fof(f78,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f33,f36,f35,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK6(X0,X1),X3),X0)
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f88,plain,(
    ! [X14,X15] :
      ( r2_hidden(k4_tarski(X14,sK10(X14,X15,sK1)),sK1)
      | ~ r2_hidden(X14,k10_relat_1(sK1,X15)) ) ),
    inference(resolution,[],[f46,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK10(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2)
            & r2_hidden(sK10(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK10(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2)
        & r2_hidden(sK10(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f253,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1,sK1),k2_relat_1(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(X0,k10_relat_1(sK1,X1)) ) ),
    inference(superposition,[],[f123,f80])).

fof(f80,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f123,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK10(X3,X5,sK1),k9_relat_1(sK1,X4))
      | ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X3,k10_relat_1(sK1,X5)) ) ),
    inference(resolution,[],[f94,f88])).

fof(f94,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(k4_tarski(X11,X13),sK1)
      | ~ r2_hidden(X11,X12)
      | r2_hidden(X13,k9_relat_1(sK1,X12)) ) ),
    inference(subsumption_resolution,[],[f87,f78])).

fof(f87,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(X11,X12)
      | ~ r2_hidden(k4_tarski(X11,X13),sK1)
      | ~ r2_hidden(X11,k1_relat_1(sK1))
      | r2_hidden(X13,k9_relat_1(sK1,X12)) ) ),
    inference(resolution,[],[f46,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
            & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)
        & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK10(sK5(X0,k10_relat_1(sK1,X1)),X1,sK1),X2)
      | ~ r1_xboole_0(X2,X1)
      | r1_xboole_0(X0,k10_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f100,f61])).

fof(f100,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK10(sK5(X2,k10_relat_1(sK1,X3)),X3,sK1),X3)
      | r1_xboole_0(X2,k10_relat_1(sK1,X3)) ) ),
    inference(resolution,[],[f89,f60])).

fof(f89,plain,(
    ! [X17,X16] :
      ( ~ r2_hidden(X16,k10_relat_1(sK1,X17))
      | r2_hidden(sK10(X16,X17,sK1),X17) ) ),
    inference(resolution,[],[f46,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK10(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f48,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | ~ r1_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f2984,plain,(
    ~ r2_hidden(sK5(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) ),
    inference(superposition,[],[f2860,f80])).

fof(f2860,plain,(
    ! [X0] : ~ r2_hidden(sK5(k2_relat_1(sK1),sK0),k9_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f2705,f2781])).

fof(f2781,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X11,sK0)
      | ~ r2_hidden(X11,k9_relat_1(sK1,X12)) ) ),
    inference(subsumption_resolution,[],[f2752,f686])).

fof(f686,plain,(
    ! [X2] : ~ r2_hidden(X2,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f678])).

fof(f678,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_xboole_0)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f673,f414])).

fof(f414,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(X2,k1_relat_1(sK1))
      | ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f385,f61])).

fof(f385,plain,(
    ! [X6] :
      ( r2_hidden(X6,k1_relat_1(sK1))
      | ~ r2_hidden(X6,k1_xboole_0) ) ),
    inference(superposition,[],[f112,f349])).

fof(f673,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(duplicate_literal_removal,[],[f665])).

fof(f665,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_xboole_0,X0)
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f470,f382])).

fof(f382,plain,(
    ! [X3] :
      ( r2_hidden(sK10(sK5(k1_xboole_0,X3),k1_xboole_0,sK1),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f101,f349])).

fof(f101,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK10(sK5(k10_relat_1(sK1,X4),X5),X4,sK1),X4)
      | r1_xboole_0(k10_relat_1(sK1,X4),X5) ) ),
    inference(resolution,[],[f89,f59])).

fof(f470,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(sK10(sK5(k1_xboole_0,X24),k1_xboole_0,sK1),X25)
      | r1_xboole_0(k1_xboole_0,X24) ) ),
    inference(resolution,[],[f453,f59])).

fof(f453,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(sK10(X0,k1_xboole_0,sK1),X1) ) ),
    inference(subsumption_resolution,[],[f452,f51])).

fof(f452,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r1_xboole_0(X1,k1_xboole_0)
      | ~ r2_hidden(sK10(X0,k1_xboole_0,sK1),X1) ) ),
    inference(resolution,[],[f379,f61])).

fof(f379,plain,(
    ! [X0] :
      ( r2_hidden(sK10(X0,k1_xboole_0,sK1),k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f89,f349])).

fof(f2752,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK9(X11,X12,sK1),k1_xboole_0)
      | ~ r2_hidden(X11,sK0)
      | ~ r2_hidden(X11,k9_relat_1(sK1,X12)) ) ),
    inference(superposition,[],[f116,f2700])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X2,sK1),k10_relat_1(sK1,X1))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X2)) ) ),
    inference(resolution,[],[f91,f85])).

fof(f85,plain,(
    ! [X8,X7] :
      ( r2_hidden(k4_tarski(sK9(X7,X8,sK1),X7),sK1)
      | ~ r2_hidden(X7,k9_relat_1(sK1,X8)) ) ),
    inference(resolution,[],[f46,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ! [X23,X21,X22] :
      ( ~ r2_hidden(k4_tarski(X23,X21),sK1)
      | ~ r2_hidden(X21,X22)
      | r2_hidden(X23,k10_relat_1(sK1,X22)) ) ),
    inference(resolution,[],[f46,f75])).

fof(f75,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | r2_hidden(X6,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2705,plain,(
    r2_hidden(sK5(k2_relat_1(sK1),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f2702,f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:35:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (12008)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (12004)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.48  % (11995)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (11993)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (12004)Refutation not found, incomplete strategy% (12004)------------------------------
% 0.22/0.49  % (12004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (12004)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (12004)Memory used [KB]: 10618
% 0.22/0.49  % (12004)Time elapsed: 0.080 s
% 0.22/0.49  % (12004)------------------------------
% 0.22/0.49  % (12004)------------------------------
% 0.22/0.49  % (12010)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (11998)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (12000)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (12005)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (11994)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (11994)Refutation not found, incomplete strategy% (11994)------------------------------
% 0.22/0.50  % (11994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (11994)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (11994)Memory used [KB]: 10618
% 0.22/0.50  % (11994)Time elapsed: 0.096 s
% 0.22/0.50  % (11994)------------------------------
% 0.22/0.50  % (11994)------------------------------
% 0.22/0.51  % (12006)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (12002)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (12011)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (12001)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.52  % (11996)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (11997)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.52  % (12003)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (11999)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.53  % (12012)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.53  % (12007)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.53  % (12013)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.53  % (12013)Refutation not found, incomplete strategy% (12013)------------------------------
% 0.22/0.53  % (12013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (12013)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (12013)Memory used [KB]: 10618
% 0.22/0.53  % (12013)Time elapsed: 0.134 s
% 0.22/0.53  % (12013)------------------------------
% 0.22/0.53  % (12013)------------------------------
% 0.22/0.54  % (12008)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f2986,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f2984,f2704])).
% 0.22/0.54  fof(f2704,plain,(
% 0.22/0.54    r2_hidden(sK5(k2_relat_1(sK1),sK0),k2_relat_1(sK1))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f2702,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.54  fof(f2702,plain,(
% 0.22/0.54    ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f2701])).
% 0.22/0.54  fof(f2701,plain,(
% 0.22/0.54    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.22/0.54    inference(backward_demodulation,[],[f48,f2700])).
% 0.22/0.54  fof(f2700,plain,(
% 0.22/0.54    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f2686])).
% 0.22/0.54  fof(f2686,plain,(
% 0.22/0.54    k1_xboole_0 = k10_relat_1(sK1,sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.22/0.54    inference(resolution,[],[f2616,f361])).
% 0.22/0.54  fof(f361,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.22/0.54    inference(backward_demodulation,[],[f348,f349])).
% 0.22/0.54  fof(f349,plain,(
% 0.22/0.54    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f51,f348])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.54  fof(f348,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_xboole_0(X0,X0) | k10_relat_1(sK1,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f339])).
% 1.42/0.54  fof(f339,plain,(
% 1.42/0.54    ( ! [X0] : (~r1_xboole_0(X0,X0) | k10_relat_1(sK1,k1_xboole_0) = X0 | k10_relat_1(sK1,k1_xboole_0) = X0) )),
% 1.42/0.54    inference(resolution,[],[f285,f284])).
% 1.42/0.54  fof(f284,plain,(
% 1.42/0.54    ( ! [X0] : (r2_hidden(sK2(sK1,k1_xboole_0,X0),X0) | k10_relat_1(sK1,k1_xboole_0) = X0) )),
% 1.42/0.54    inference(resolution,[],[f283,f51])).
% 1.42/0.54  fof(f283,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | k10_relat_1(sK1,X0) = X1 | r2_hidden(sK2(sK1,X0,X1),X1)) )),
% 1.42/0.54    inference(duplicate_literal_removal,[],[f282])).
% 1.42/0.54  fof(f282,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k10_relat_1(sK1,X0) = X1 | ~r1_xboole_0(X0,X0) | r2_hidden(sK2(sK1,X0,X1),X1) | r2_hidden(sK2(sK1,X0,X1),X1) | k10_relat_1(sK1,X0) = X1) )),
% 1.42/0.54    inference(resolution,[],[f128,f83])).
% 1.42/0.54  fof(f83,plain,(
% 1.42/0.54    ( ! [X2,X3] : (r2_hidden(sK3(sK1,X2,X3),X2) | r2_hidden(sK2(sK1,X2,X3),X3) | k10_relat_1(sK1,X2) = X3) )),
% 1.42/0.54    inference(resolution,[],[f46,f57])).
% 1.42/0.54  fof(f57,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 1.42/0.54    inference(cnf_transformation,[],[f29])).
% 1.42/0.54  fof(f29,plain,(
% 1.42/0.54    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f28,f27,f26])).
% 1.42/0.54  fof(f26,plain,(
% 1.42/0.54    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),X4),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f27,plain,(
% 1.42/0.54    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X5),X0)) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f28,plain,(
% 1.42/0.54    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK4(X0,X1,X6)),X0)))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f25,plain,(
% 1.42/0.54    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.42/0.54    inference(rectify,[],[f24])).
% 1.42/0.54  fof(f24,plain,(
% 1.42/0.54    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.42/0.54    inference(nnf_transformation,[],[f15])).
% 1.42/0.54  fof(f15,plain,(
% 1.42/0.54    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f4])).
% 1.42/0.54  fof(f4,axiom,(
% 1.42/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 1.42/0.54  fof(f46,plain,(
% 1.42/0.54    v1_relat_1(sK1)),
% 1.42/0.54    inference(cnf_transformation,[],[f23])).
% 1.42/0.54  fof(f23,plain,(
% 1.42/0.54    (~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 1.42/0.54  fof(f22,plain,(
% 1.42/0.54    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f21,plain,(
% 1.42/0.54    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.42/0.54    inference(flattening,[],[f20])).
% 1.42/0.54  fof(f20,plain,(
% 1.42/0.54    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 1.42/0.54    inference(nnf_transformation,[],[f13])).
% 1.42/0.54  fof(f13,plain,(
% 1.42/0.54    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.42/0.54    inference(ennf_transformation,[],[f11])).
% 1.42/0.54  fof(f11,negated_conjecture,(
% 1.42/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.42/0.54    inference(negated_conjecture,[],[f10])).
% 1.42/0.54  fof(f10,conjecture,(
% 1.42/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.42/0.54  fof(f128,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK3(sK1,X0,X1),X2) | k10_relat_1(sK1,X0) = X1 | ~r1_xboole_0(X2,X0) | r2_hidden(sK2(sK1,X0,X1),X1)) )),
% 1.42/0.54    inference(resolution,[],[f83,f61])).
% 1.42/0.54  fof(f61,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f31])).
% 1.42/0.54  fof(f285,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~r2_hidden(sK2(sK1,k1_xboole_0,X0),X1) | ~r1_xboole_0(X1,X0) | k10_relat_1(sK1,k1_xboole_0) = X0) )),
% 1.42/0.54    inference(resolution,[],[f284,f61])).
% 1.42/0.54  fof(f2616,plain,(
% 1.42/0.54    ( ! [X0] : (r1_xboole_0(X0,k10_relat_1(sK1,sK0)) | k1_xboole_0 = k10_relat_1(sK1,sK0)) )),
% 1.42/0.54    inference(resolution,[],[f2605,f47])).
% 1.42/0.54  fof(f47,plain,(
% 1.42/0.54    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.42/0.54    inference(cnf_transformation,[],[f23])).
% 1.42/0.54  fof(f2605,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(sK1),X0) | r1_xboole_0(X1,k10_relat_1(sK1,X0))) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f2593,f60])).
% 1.42/0.54  fof(f60,plain,(
% 1.42/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f31])).
% 1.42/0.54  fof(f2593,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(sK1),X0) | r1_xboole_0(X1,k10_relat_1(sK1,X0)) | ~r2_hidden(sK5(X1,k10_relat_1(sK1,X0)),k10_relat_1(sK1,X0))) )),
% 1.42/0.54    inference(resolution,[],[f160,f254])).
% 1.42/0.54  fof(f254,plain,(
% 1.42/0.54    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1,sK1),k2_relat_1(sK1)) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f253,f112])).
% 1.42/0.54  fof(f112,plain,(
% 1.42/0.54    ( ! [X4,X3] : (~r2_hidden(X3,k10_relat_1(sK1,X4)) | r2_hidden(X3,k1_relat_1(sK1))) )),
% 1.42/0.54    inference(resolution,[],[f88,f78])).
% 1.42/0.54  fof(f78,plain,(
% 1.42/0.54    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 1.42/0.54    inference(equality_resolution,[],[f63])).
% 1.42/0.54  fof(f63,plain,(
% 1.42/0.54    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 1.42/0.54    inference(cnf_transformation,[],[f37])).
% 1.42/0.54  fof(f37,plain,(
% 1.42/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f33,f36,f35,f34])).
% 1.42/0.54  fof(f34,plain,(
% 1.42/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK6(X0,X1),X3),X0) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) | r2_hidden(sK6(X0,X1),X1))))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f35,plain,(
% 1.42/0.54    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK6(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f36,plain,(
% 1.42/0.54    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK8(X0,X5)),X0))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f33,plain,(
% 1.42/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.42/0.54    inference(rectify,[],[f32])).
% 1.42/0.54  fof(f32,plain,(
% 1.42/0.54    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.42/0.54    inference(nnf_transformation,[],[f5])).
% 1.42/0.54  fof(f5,axiom,(
% 1.42/0.54    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.42/0.54  fof(f88,plain,(
% 1.42/0.54    ( ! [X14,X15] : (r2_hidden(k4_tarski(X14,sK10(X14,X15,sK1)),sK1) | ~r2_hidden(X14,k10_relat_1(sK1,X15))) )),
% 1.42/0.54    inference(resolution,[],[f46,f72])).
% 1.42/0.54  fof(f72,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f45,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2) & r2_hidden(sK10(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f43,f44])).
% 1.42/0.54  fof(f44,plain,(
% 1.42/0.54    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK10(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK10(X0,X1,X2)),X2) & r2_hidden(sK10(X0,X1,X2),k2_relat_1(X2))))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f43,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.42/0.54    inference(rectify,[],[f42])).
% 1.42/0.54  fof(f42,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.42/0.54    inference(nnf_transformation,[],[f19])).
% 1.42/0.54  fof(f19,plain,(
% 1.42/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.42/0.54    inference(ennf_transformation,[],[f8])).
% 1.42/0.54  fof(f8,axiom,(
% 1.42/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 1.42/0.54  fof(f253,plain,(
% 1.42/0.54    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1,sK1),k2_relat_1(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(X0,k10_relat_1(sK1,X1))) )),
% 1.42/0.54    inference(superposition,[],[f123,f80])).
% 1.42/0.54  fof(f80,plain,(
% 1.42/0.54    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 1.42/0.54    inference(unit_resulting_resolution,[],[f46,f52])).
% 1.42/0.54  fof(f52,plain,(
% 1.42/0.54    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f14])).
% 1.42/0.54  fof(f14,plain,(
% 1.42/0.54    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f7])).
% 1.42/0.54  fof(f7,axiom,(
% 1.42/0.54    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 1.42/0.54  fof(f123,plain,(
% 1.42/0.54    ( ! [X4,X5,X3] : (r2_hidden(sK10(X3,X5,sK1),k9_relat_1(sK1,X4)) | ~r2_hidden(X3,X4) | ~r2_hidden(X3,k10_relat_1(sK1,X5))) )),
% 1.42/0.54    inference(resolution,[],[f94,f88])).
% 1.42/0.54  fof(f94,plain,(
% 1.42/0.54    ( ! [X12,X13,X11] : (~r2_hidden(k4_tarski(X11,X13),sK1) | ~r2_hidden(X11,X12) | r2_hidden(X13,k9_relat_1(sK1,X12))) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f87,f78])).
% 1.42/0.54  fof(f87,plain,(
% 1.42/0.54    ( ! [X12,X13,X11] : (~r2_hidden(X11,X12) | ~r2_hidden(k4_tarski(X11,X13),sK1) | ~r2_hidden(X11,k1_relat_1(sK1)) | r2_hidden(X13,k9_relat_1(sK1,X12))) )),
% 1.42/0.54    inference(resolution,[],[f46,f70])).
% 1.42/0.54  fof(f70,plain,(
% 1.42/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f41])).
% 1.42/0.54  fof(f41,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f39,f40])).
% 1.42/0.54  fof(f40,plain,(
% 1.42/0.54    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X2))))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f39,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.42/0.54    inference(rectify,[],[f38])).
% 1.42/0.54  fof(f38,plain,(
% 1.42/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.42/0.54    inference(nnf_transformation,[],[f18])).
% 1.42/0.54  fof(f18,plain,(
% 1.42/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.42/0.54    inference(ennf_transformation,[],[f6])).
% 1.42/0.54  fof(f6,axiom,(
% 1.42/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.42/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 1.42/0.54  fof(f160,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK10(sK5(X0,k10_relat_1(sK1,X1)),X1,sK1),X2) | ~r1_xboole_0(X2,X1) | r1_xboole_0(X0,k10_relat_1(sK1,X1))) )),
% 1.42/0.54    inference(resolution,[],[f100,f61])).
% 1.42/0.54  fof(f100,plain,(
% 1.42/0.54    ( ! [X2,X3] : (r2_hidden(sK10(sK5(X2,k10_relat_1(sK1,X3)),X3,sK1),X3) | r1_xboole_0(X2,k10_relat_1(sK1,X3))) )),
% 1.42/0.54    inference(resolution,[],[f89,f60])).
% 1.42/0.54  fof(f89,plain,(
% 1.42/0.54    ( ! [X17,X16] : (~r2_hidden(X16,k10_relat_1(sK1,X17)) | r2_hidden(sK10(X16,X17,sK1),X17)) )),
% 1.42/0.54    inference(resolution,[],[f46,f73])).
% 1.42/0.54  fof(f73,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK10(X0,X1,X2),X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f48,plain,(
% 1.42/0.54    k1_xboole_0 != k10_relat_1(sK1,sK0) | ~r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.42/0.54    inference(cnf_transformation,[],[f23])).
% 1.42/0.54  fof(f2984,plain,(
% 1.42/0.54    ~r2_hidden(sK5(k2_relat_1(sK1),sK0),k2_relat_1(sK1))),
% 1.42/0.54    inference(superposition,[],[f2860,f80])).
% 1.42/0.54  fof(f2860,plain,(
% 1.42/0.54    ( ! [X0] : (~r2_hidden(sK5(k2_relat_1(sK1),sK0),k9_relat_1(sK1,X0))) )),
% 1.42/0.54    inference(unit_resulting_resolution,[],[f2705,f2781])).
% 1.42/0.54  fof(f2781,plain,(
% 1.42/0.54    ( ! [X12,X11] : (~r2_hidden(X11,sK0) | ~r2_hidden(X11,k9_relat_1(sK1,X12))) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f2752,f686])).
% 1.42/0.54  fof(f686,plain,(
% 1.42/0.54    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0)) )),
% 1.42/0.54    inference(duplicate_literal_removal,[],[f678])).
% 1.42/0.54  fof(f678,plain,(
% 1.42/0.54    ( ! [X2] : (~r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k1_xboole_0)) )),
% 1.42/0.54    inference(resolution,[],[f673,f414])).
% 1.42/0.54  fof(f414,plain,(
% 1.42/0.54    ( ! [X2,X1] : (~r1_xboole_0(X2,k1_relat_1(sK1)) | ~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X2)) )),
% 1.42/0.54    inference(resolution,[],[f385,f61])).
% 1.42/0.54  fof(f385,plain,(
% 1.42/0.54    ( ! [X6] : (r2_hidden(X6,k1_relat_1(sK1)) | ~r2_hidden(X6,k1_xboole_0)) )),
% 1.42/0.54    inference(superposition,[],[f112,f349])).
% 1.42/0.54  fof(f673,plain,(
% 1.42/0.54    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.42/0.54    inference(duplicate_literal_removal,[],[f665])).
% 1.42/0.54  fof(f665,plain,(
% 1.42/0.54    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0) | r1_xboole_0(k1_xboole_0,X0)) )),
% 1.42/0.54    inference(resolution,[],[f470,f382])).
% 1.42/0.54  fof(f382,plain,(
% 1.42/0.54    ( ! [X3] : (r2_hidden(sK10(sK5(k1_xboole_0,X3),k1_xboole_0,sK1),k1_xboole_0) | r1_xboole_0(k1_xboole_0,X3)) )),
% 1.42/0.54    inference(superposition,[],[f101,f349])).
% 1.42/0.54  fof(f101,plain,(
% 1.42/0.54    ( ! [X4,X5] : (r2_hidden(sK10(sK5(k10_relat_1(sK1,X4),X5),X4,sK1),X4) | r1_xboole_0(k10_relat_1(sK1,X4),X5)) )),
% 1.42/0.54    inference(resolution,[],[f89,f59])).
% 1.42/0.54  fof(f470,plain,(
% 1.42/0.54    ( ! [X24,X25] : (~r2_hidden(sK10(sK5(k1_xboole_0,X24),k1_xboole_0,sK1),X25) | r1_xboole_0(k1_xboole_0,X24)) )),
% 1.42/0.54    inference(resolution,[],[f453,f59])).
% 1.42/0.54  fof(f453,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(sK10(X0,k1_xboole_0,sK1),X1)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f452,f51])).
% 1.42/0.54  fof(f452,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r1_xboole_0(X1,k1_xboole_0) | ~r2_hidden(sK10(X0,k1_xboole_0,sK1),X1)) )),
% 1.42/0.54    inference(resolution,[],[f379,f61])).
% 1.42/0.54  fof(f379,plain,(
% 1.42/0.54    ( ! [X0] : (r2_hidden(sK10(X0,k1_xboole_0,sK1),k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.42/0.54    inference(superposition,[],[f89,f349])).
% 1.42/0.54  fof(f2752,plain,(
% 1.42/0.54    ( ! [X12,X11] : (r2_hidden(sK9(X11,X12,sK1),k1_xboole_0) | ~r2_hidden(X11,sK0) | ~r2_hidden(X11,k9_relat_1(sK1,X12))) )),
% 1.42/0.54    inference(superposition,[],[f116,f2700])).
% 1.42/0.54  fof(f116,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X2,sK1),k10_relat_1(sK1,X1)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k9_relat_1(sK1,X2))) )),
% 1.42/0.54    inference(resolution,[],[f91,f85])).
% 1.42/0.54  fof(f85,plain,(
% 1.42/0.54    ( ! [X8,X7] : (r2_hidden(k4_tarski(sK9(X7,X8,sK1),X7),sK1) | ~r2_hidden(X7,k9_relat_1(sK1,X8))) )),
% 1.42/0.54    inference(resolution,[],[f46,f68])).
% 1.42/0.54  fof(f68,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK9(X0,X1,X2),X0),X2)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f41])).
% 1.42/0.54  fof(f91,plain,(
% 1.42/0.54    ( ! [X23,X21,X22] : (~r2_hidden(k4_tarski(X23,X21),sK1) | ~r2_hidden(X21,X22) | r2_hidden(X23,k10_relat_1(sK1,X22))) )),
% 1.42/0.54    inference(resolution,[],[f46,f75])).
% 1.42/0.54  fof(f75,plain,(
% 1.42/0.54    ( ! [X6,X0,X7,X1] : (~v1_relat_1(X0) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | r2_hidden(X6,k10_relat_1(X0,X1))) )),
% 1.42/0.54    inference(equality_resolution,[],[f55])).
% 1.42/0.54  fof(f55,plain,(
% 1.42/0.54    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f29])).
% 1.42/0.54  fof(f2705,plain,(
% 1.42/0.54    r2_hidden(sK5(k2_relat_1(sK1),sK0),sK0)),
% 1.42/0.54    inference(unit_resulting_resolution,[],[f2702,f60])).
% 1.42/0.54  % SZS output end Proof for theBenchmark
% 1.42/0.54  % (12008)------------------------------
% 1.42/0.54  % (12008)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (12008)Termination reason: Refutation
% 1.42/0.54  
% 1.42/0.54  % (12008)Memory used [KB]: 9083
% 1.42/0.54  % (12008)Time elapsed: 0.120 s
% 1.42/0.54  % (12008)------------------------------
% 1.42/0.54  % (12008)------------------------------
% 1.42/0.54  % (12009)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.42/0.54  % (11992)Success in time 0.18 s
%------------------------------------------------------------------------------
