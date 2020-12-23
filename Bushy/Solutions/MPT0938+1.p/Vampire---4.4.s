%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord2__t3_wellord2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:17 EDT 2019

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 151 expanded)
%              Number of leaves         :    9 (  35 expanded)
%              Depth                    :   26
%              Number of atoms          :  353 (1096 expanded)
%              Number of equality atoms :   28 (  95 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2097,plain,(
    $false ),
    inference(resolution,[],[f2080,f64])).

fof(f64,plain,(
    ~ v8_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ~ v8_relat_2(k1_wellord2(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f49])).

fof(f49,plain,
    ( ? [X0] : ~ v8_relat_2(k1_wellord2(X0))
   => ~ v8_relat_2(k1_wellord2(sK0)) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] : ~ v8_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t3_wellord2.p',t3_wellord2)).

fof(f2080,plain,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(resolution,[],[f2063,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r8_relat_2(k1_wellord2(X0),X0)
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f124,f66])).

fof(f66,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t3_wellord2.p',dt_k1_wellord2)).

fof(f124,plain,(
    ! [X0] :
      ( ~ r8_relat_2(k1_wellord2(X0),X0)
      | v8_relat_2(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f69,f107])).

fof(f107,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f104,f66])).

fof(f104,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK5(X0,X1),sK6(X0,X1))
              | ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
            & ( r1_tarski(sK5(X0,X1),sK6(X0,X1))
              | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
            & r2_hidden(sK6(X0,X1),X0)
            & r2_hidden(sK5(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f60,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK5(X0,X1),sK6(X0,X1))
          | ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
        & ( r1_tarski(sK5(X0,X1),sK6(X0,X1))
          | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
        & r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t3_wellord2.p',d1_wellord2)).

fof(f69,plain,(
    ! [X0] :
      ( ~ r8_relat_2(X0,k3_relat_1(X0))
      | v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ~ r8_relat_2(X0,k3_relat_1(X0)) )
        & ( r8_relat_2(X0,k3_relat_1(X0))
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> r8_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t3_wellord2.p',d16_relat_2)).

fof(f2063,plain,(
    ! [X0] : r8_relat_2(k1_wellord2(X0),X0) ),
    inference(subsumption_resolution,[],[f2062,f66])).

fof(f2062,plain,(
    ! [X0] :
      ( r8_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f2059])).

fof(f2059,plain,(
    ! [X0] :
      ( r8_relat_2(k1_wellord2(X0),X0)
      | r8_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f2046,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
              & r2_hidden(sK3(X0,X1),X1)
              & r2_hidden(sK2(X0,X1),X1)
              & r2_hidden(sK1(X0,X1),X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2,X3,X4] :
          ( ~ r2_hidden(k4_tarski(X2,X4),X0)
          & r2_hidden(k4_tarski(X3,X4),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X4,X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3,X4] :
                ( r2_hidden(k4_tarski(X2,X4),X0)
                | ~ r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => r2_hidden(k4_tarski(X2,X4),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t3_wellord2.p',d8_relat_2)).

fof(f2046,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k1_wellord2(X0),X0),X0)
      | r8_relat_2(k1_wellord2(X0),X0) ) ),
    inference(subsumption_resolution,[],[f2045,f66])).

fof(f2045,plain,(
    ! [X0] :
      ( r8_relat_2(k1_wellord2(X0),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0),X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f2042])).

fof(f2042,plain,(
    ! [X0] :
      ( r8_relat_2(k1_wellord2(X0),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0),X0),X0)
      | r8_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f1586,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1586,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k1_wellord2(X0),X0),X0)
      | r8_relat_2(k1_wellord2(X0),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0),X0),X0) ) ),
    inference(subsumption_resolution,[],[f1585,f66])).

fof(f1585,plain,(
    ! [X0] :
      ( r8_relat_2(k1_wellord2(X0),X0)
      | ~ r2_hidden(sK2(k1_wellord2(X0),X0),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0),X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f1580])).

fof(f1580,plain,(
    ! [X0] :
      ( r8_relat_2(k1_wellord2(X0),X0)
      | ~ r2_hidden(sK2(k1_wellord2(X0),X0),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0),X0),X0)
      | r8_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f666,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f666,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK3(k1_wellord2(X6),X7),X6)
      | r8_relat_2(k1_wellord2(X6),X7)
      | ~ r2_hidden(sK2(k1_wellord2(X6),X7),X6)
      | ~ r2_hidden(sK1(k1_wellord2(X6),X7),X6) ) ),
    inference(subsumption_resolution,[],[f665,f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1))
      | ~ r2_hidden(sK3(k1_wellord2(X0),X1),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | r8_relat_2(k1_wellord2(X0),X1) ) ),
    inference(subsumption_resolution,[],[f175,f66])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0),X1),sK3(k1_wellord2(X0),X1))
      | ~ r2_hidden(sK3(k1_wellord2(X0),X1),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | r8_relat_2(k1_wellord2(X0),X1)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f105,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK3(X0,X1)),X0)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f105,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f102,f66])).

fof(f102,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f665,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK2(k1_wellord2(X6),X7),X6)
      | r8_relat_2(k1_wellord2(X6),X7)
      | r1_tarski(sK1(k1_wellord2(X6),X7),sK3(k1_wellord2(X6),X7))
      | ~ r2_hidden(sK3(k1_wellord2(X6),X7),X6)
      | ~ r2_hidden(sK1(k1_wellord2(X6),X7),X6) ) ),
    inference(duplicate_literal_removal,[],[f654])).

fof(f654,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK2(k1_wellord2(X6),X7),X6)
      | r8_relat_2(k1_wellord2(X6),X7)
      | r1_tarski(sK1(k1_wellord2(X6),X7),sK3(k1_wellord2(X6),X7))
      | ~ r2_hidden(sK3(k1_wellord2(X6),X7),X6)
      | ~ r2_hidden(sK2(k1_wellord2(X6),X7),X6)
      | ~ r2_hidden(sK1(k1_wellord2(X6),X7),X6)
      | r8_relat_2(k1_wellord2(X6),X7) ) ),
    inference(resolution,[],[f334,f184])).

fof(f184,plain,(
    ! [X4,X3] :
      ( r1_tarski(sK1(k1_wellord2(X3),X4),sK2(k1_wellord2(X3),X4))
      | ~ r2_hidden(sK2(k1_wellord2(X3),X4),X3)
      | ~ r2_hidden(sK1(k1_wellord2(X3),X4),X3)
      | r8_relat_2(k1_wellord2(X3),X4) ) ),
    inference(subsumption_resolution,[],[f181,f66])).

fof(f181,plain,(
    ! [X4,X3] :
      ( r1_tarski(sK1(k1_wellord2(X3),X4),sK2(k1_wellord2(X3),X4))
      | ~ r2_hidden(sK2(k1_wellord2(X3),X4),X3)
      | ~ r2_hidden(sK1(k1_wellord2(X3),X4),X3)
      | r8_relat_2(k1_wellord2(X3),X4)
      | ~ v1_relat_1(k1_wellord2(X3)) ) ),
    inference(resolution,[],[f106,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f106,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f103,f66])).

fof(f103,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f334,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_tarski(X8,sK2(k1_wellord2(X6),X7))
      | ~ r2_hidden(sK2(k1_wellord2(X6),X7),X6)
      | r8_relat_2(k1_wellord2(X6),X7)
      | r1_tarski(X8,sK3(k1_wellord2(X6),X7))
      | ~ r2_hidden(sK3(k1_wellord2(X6),X7),X6) ) ),
    inference(resolution,[],[f185,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/wellord2__t3_wellord2.p',t1_xboole_1)).

fof(f185,plain,(
    ! [X6,X5] :
      ( r1_tarski(sK2(k1_wellord2(X5),X6),sK3(k1_wellord2(X5),X6))
      | ~ r2_hidden(sK3(k1_wellord2(X5),X6),X5)
      | ~ r2_hidden(sK2(k1_wellord2(X5),X6),X5)
      | r8_relat_2(k1_wellord2(X5),X6) ) ),
    inference(subsumption_resolution,[],[f182,f66])).

fof(f182,plain,(
    ! [X6,X5] :
      ( r1_tarski(sK2(k1_wellord2(X5),X6),sK3(k1_wellord2(X5),X6))
      | ~ r2_hidden(sK3(k1_wellord2(X5),X6),X5)
      | ~ r2_hidden(sK2(k1_wellord2(X5),X6),X5)
      | r8_relat_2(k1_wellord2(X5),X6)
      | ~ v1_relat_1(k1_wellord2(X5)) ) ),
    inference(resolution,[],[f106,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
