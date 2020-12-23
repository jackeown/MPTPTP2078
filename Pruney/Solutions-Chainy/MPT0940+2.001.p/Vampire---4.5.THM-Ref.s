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
% DateTime   : Thu Dec  3 12:59:59 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 153 expanded)
%              Number of leaves         :    9 (  36 expanded)
%              Depth                    :   26
%              Number of atoms          :  312 ( 962 expanded)
%              Number of equality atoms :   56 ( 171 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(subsumption_resolution,[],[f100,f28])).

fof(f28,plain,(
    ~ v4_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ~ v4_relat_2(k1_wellord2(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f14])).

fof(f14,plain,
    ( ? [X0] : ~ v4_relat_2(k1_wellord2(X0))
   => ~ v4_relat_2(k1_wellord2(sK0)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : ~ v4_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : v4_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord2)).

fof(f100,plain,(
    v4_relat_2(k1_wellord2(sK0)) ),
    inference(resolution,[],[f99,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r4_relat_2(k1_wellord2(X0),X0)
      | v4_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f60,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f60,plain,(
    ! [X0] :
      ( ~ r4_relat_2(k1_wellord2(X0),X0)
      | v4_relat_2(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f31,f59])).

fof(f59,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f29,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & r2_hidden(sK4(X0,X1),X0)
            & r2_hidden(sK3(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f31,plain,(
    ! [X0] :
      ( ~ r4_relat_2(X0,k3_relat_1(X0))
      | v4_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v4_relat_2(X0)
          | ~ r4_relat_2(X0,k3_relat_1(X0)) )
        & ( r4_relat_2(X0,k3_relat_1(X0))
          | ~ v4_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v4_relat_2(X0)
      <=> r4_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_2)).

fof(f99,plain,(
    r4_relat_2(k1_wellord2(sK0),sK0) ),
    inference(subsumption_resolution,[],[f94,f29])).

fof(f94,plain,
    ( r4_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,
    ( sK1(k1_wellord2(sK0),sK0) != sK1(k1_wellord2(sK0),sK0)
    | r4_relat_2(k1_wellord2(sK0),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0)) ),
    inference(superposition,[],[f37,f83])).

fof(f83,plain,(
    sK1(k1_wellord2(sK0),sK0) = sK2(k1_wellord2(sK0),sK0) ),
    inference(resolution,[],[f80,f28])).

fof(f80,plain,(
    ! [X0] :
      ( v4_relat_2(k1_wellord2(X0))
      | sK1(k1_wellord2(X0),X0) = sK2(k1_wellord2(X0),X0) ) ),
    inference(resolution,[],[f79,f61])).

fof(f79,plain,(
    ! [X0] :
      ( r4_relat_2(k1_wellord2(X0),X0)
      | sK1(k1_wellord2(X0),X0) = sK2(k1_wellord2(X0),X0) ) ),
    inference(subsumption_resolution,[],[f78,f29])).

fof(f78,plain,(
    ! [X0] :
      ( r4_relat_2(k1_wellord2(X0),X0)
      | sK1(k1_wellord2(X0),X0) = sK2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( r4_relat_2(k1_wellord2(X0),X0)
      | sK1(k1_wellord2(X0),X0) = sK2(k1_wellord2(X0),X0)
      | r4_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f76,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r4_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ( sK1(X0,X1) != sK2(X0,X1)
              & r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
              & r2_hidden(sK2(X0,X1),X1)
              & r2_hidden(sK1(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( X4 = X5
                | ~ r2_hidden(k4_tarski(X5,X4),X0)
                | ~ r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & r2_hidden(k4_tarski(X3,X2),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( sK1(X0,X1) != sK2(X0,X1)
        & r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ? [X2,X3] :
                ( X2 != X3
                & r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( X4 = X5
                | ~ r2_hidden(k4_tarski(X5,X4),X0)
                | ~ r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ? [X2,X3] :
                ( X2 != X3
                & r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( X2 = X3
                | ~ r2_hidden(k4_tarski(X3,X2),X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r4_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).

fof(f76,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k1_wellord2(X0),X0),X0)
      | r4_relat_2(k1_wellord2(X0),X0)
      | sK1(k1_wellord2(X0),X0) = sK2(k1_wellord2(X0),X0) ) ),
    inference(subsumption_resolution,[],[f75,f29])).

fof(f75,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k1_wellord2(X0),X0),X0)
      | r4_relat_2(k1_wellord2(X0),X0)
      | sK1(k1_wellord2(X0),X0) = sK2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k1_wellord2(X0),X0),X0)
      | r4_relat_2(k1_wellord2(X0),X0)
      | sK1(k1_wellord2(X0),X0) = sK2(k1_wellord2(X0),X0)
      | r4_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f73,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r4_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | r4_relat_2(k1_wellord2(X0),X1)
      | sK1(k1_wellord2(X0),X1) = sK2(k1_wellord2(X0),X1) ) ),
    inference(subsumption_resolution,[],[f72,f69])).

fof(f69,plain,(
    ! [X4,X3] :
      ( r1_tarski(sK1(k1_wellord2(X3),X4),sK2(k1_wellord2(X3),X4))
      | ~ r2_hidden(sK1(k1_wellord2(X3),X4),X3)
      | ~ r2_hidden(sK2(k1_wellord2(X3),X4),X3)
      | r4_relat_2(k1_wellord2(X3),X4) ) ),
    inference(subsumption_resolution,[],[f66,f29])).

fof(f66,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(sK1(k1_wellord2(X3),X4),X3)
      | r1_tarski(sK1(k1_wellord2(X3),X4),sK2(k1_wellord2(X3),X4))
      | ~ r2_hidden(sK2(k1_wellord2(X3),X4),X3)
      | r4_relat_2(k1_wellord2(X3),X4)
      | ~ v1_relat_1(k1_wellord2(X3)) ) ),
    inference(resolution,[],[f58,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r4_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X4,X0)
      | r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0) ) ),
    inference(global_subsumption,[],[f29,f53])).

fof(f53,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | r4_relat_2(k1_wellord2(X0),X1)
      | ~ r1_tarski(sK1(k1_wellord2(X0),X1),sK2(k1_wellord2(X0),X1))
      | sK1(k1_wellord2(X0),X1) = sK2(k1_wellord2(X0),X1) ) ),
    inference(resolution,[],[f70,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f70,plain,(
    ! [X6,X5] :
      ( r1_tarski(sK2(k1_wellord2(X5),X6),sK1(k1_wellord2(X5),X6))
      | ~ r2_hidden(sK2(k1_wellord2(X5),X6),X5)
      | ~ r2_hidden(sK1(k1_wellord2(X5),X6),X5)
      | r4_relat_2(k1_wellord2(X5),X6) ) ),
    inference(subsumption_resolution,[],[f67,f29])).

fof(f67,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(sK2(k1_wellord2(X5),X6),X5)
      | r1_tarski(sK2(k1_wellord2(X5),X6),sK1(k1_wellord2(X5),X6))
      | ~ r2_hidden(sK1(k1_wellord2(X5),X6),X5)
      | r4_relat_2(k1_wellord2(X5),X6)
      | ~ v1_relat_1(k1_wellord2(X5)) ) ),
    inference(resolution,[],[f58,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | r4_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != sK2(X0,X1)
      | r4_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:21:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (20362)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (20370)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (20362)Refutation not found, incomplete strategy% (20362)------------------------------
% 0.22/0.52  % (20362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20362)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20362)Memory used [KB]: 10618
% 0.22/0.52  % (20362)Time elapsed: 0.091 s
% 0.22/0.52  % (20362)------------------------------
% 0.22/0.52  % (20362)------------------------------
% 0.22/0.53  % (20379)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.35/0.54  % (20361)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.35/0.54  % (20371)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.35/0.54  % (20361)Refutation not found, incomplete strategy% (20361)------------------------------
% 1.35/0.54  % (20361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (20361)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (20361)Memory used [KB]: 6012
% 1.35/0.54  % (20361)Time elapsed: 0.112 s
% 1.35/0.54  % (20361)------------------------------
% 1.35/0.54  % (20361)------------------------------
% 1.35/0.55  % (20377)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.35/0.55  % (20377)Refutation found. Thanks to Tanya!
% 1.35/0.55  % SZS status Theorem for theBenchmark
% 1.35/0.55  % SZS output start Proof for theBenchmark
% 1.35/0.55  fof(f102,plain,(
% 1.35/0.55    $false),
% 1.35/0.55    inference(subsumption_resolution,[],[f100,f28])).
% 1.35/0.55  fof(f28,plain,(
% 1.35/0.55    ~v4_relat_2(k1_wellord2(sK0))),
% 1.35/0.55    inference(cnf_transformation,[],[f15])).
% 1.35/0.55  fof(f15,plain,(
% 1.35/0.55    ~v4_relat_2(k1_wellord2(sK0))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f14])).
% 1.35/0.55  fof(f14,plain,(
% 1.35/0.55    ? [X0] : ~v4_relat_2(k1_wellord2(X0)) => ~v4_relat_2(k1_wellord2(sK0))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f8,plain,(
% 1.35/0.55    ? [X0] : ~v4_relat_2(k1_wellord2(X0))),
% 1.35/0.55    inference(ennf_transformation,[],[f7])).
% 1.35/0.55  fof(f7,negated_conjecture,(
% 1.35/0.55    ~! [X0] : v4_relat_2(k1_wellord2(X0))),
% 1.35/0.55    inference(negated_conjecture,[],[f6])).
% 1.35/0.55  fof(f6,conjecture,(
% 1.35/0.55    ! [X0] : v4_relat_2(k1_wellord2(X0))),
% 1.35/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_wellord2)).
% 1.35/0.55  fof(f100,plain,(
% 1.35/0.55    v4_relat_2(k1_wellord2(sK0))),
% 1.35/0.55    inference(resolution,[],[f99,f61])).
% 1.35/0.55  fof(f61,plain,(
% 1.35/0.55    ( ! [X0] : (~r4_relat_2(k1_wellord2(X0),X0) | v4_relat_2(k1_wellord2(X0))) )),
% 1.35/0.55    inference(subsumption_resolution,[],[f60,f29])).
% 1.35/0.55  fof(f29,plain,(
% 1.35/0.55    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f5])).
% 1.35/0.55  fof(f5,axiom,(
% 1.35/0.55    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 1.35/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 1.35/0.55  fof(f60,plain,(
% 1.35/0.55    ( ! [X0] : (~r4_relat_2(k1_wellord2(X0),X0) | v4_relat_2(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.35/0.55    inference(superposition,[],[f31,f59])).
% 1.35/0.55  fof(f59,plain,(
% 1.35/0.55    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 1.35/0.55    inference(global_subsumption,[],[f29,f54])).
% 1.35/0.55  fof(f54,plain,(
% 1.35/0.55    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.35/0.55    inference(equality_resolution,[],[f38])).
% 1.35/0.55  fof(f38,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f25])).
% 1.35/0.55  fof(f25,plain,(
% 1.35/0.55    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f24])).
% 1.35/0.55  fof(f24,plain,(
% 1.35/0.55    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f23,plain,(
% 1.35/0.55    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.35/0.55    inference(rectify,[],[f22])).
% 1.35/0.55  fof(f22,plain,(
% 1.35/0.55    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.35/0.55    inference(flattening,[],[f21])).
% 1.35/0.55  fof(f21,plain,(
% 1.35/0.55    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.35/0.55    inference(nnf_transformation,[],[f13])).
% 1.35/0.55  fof(f13,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.35/0.55    inference(flattening,[],[f12])).
% 1.35/0.55  fof(f12,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.35/0.55    inference(ennf_transformation,[],[f3])).
% 1.35/0.55  fof(f3,axiom,(
% 1.35/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 1.35/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 1.35/0.55  fof(f31,plain,(
% 1.35/0.55    ( ! [X0] : (~r4_relat_2(X0,k3_relat_1(X0)) | v4_relat_2(X0) | ~v1_relat_1(X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f16])).
% 1.35/0.55  fof(f16,plain,(
% 1.35/0.55    ! [X0] : (((v4_relat_2(X0) | ~r4_relat_2(X0,k3_relat_1(X0))) & (r4_relat_2(X0,k3_relat_1(X0)) | ~v4_relat_2(X0))) | ~v1_relat_1(X0))),
% 1.35/0.55    inference(nnf_transformation,[],[f9])).
% 1.35/0.55  fof(f9,plain,(
% 1.35/0.55    ! [X0] : ((v4_relat_2(X0) <=> r4_relat_2(X0,k3_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.35/0.55    inference(ennf_transformation,[],[f2])).
% 1.35/0.55  fof(f2,axiom,(
% 1.35/0.55    ! [X0] : (v1_relat_1(X0) => (v4_relat_2(X0) <=> r4_relat_2(X0,k3_relat_1(X0))))),
% 1.35/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_2)).
% 1.35/0.55  fof(f99,plain,(
% 1.35/0.55    r4_relat_2(k1_wellord2(sK0),sK0)),
% 1.35/0.55    inference(subsumption_resolution,[],[f94,f29])).
% 1.35/0.55  fof(f94,plain,(
% 1.35/0.55    r4_relat_2(k1_wellord2(sK0),sK0) | ~v1_relat_1(k1_wellord2(sK0))),
% 1.35/0.55    inference(trivial_inequality_removal,[],[f92])).
% 1.35/0.55  fof(f92,plain,(
% 1.35/0.55    sK1(k1_wellord2(sK0),sK0) != sK1(k1_wellord2(sK0),sK0) | r4_relat_2(k1_wellord2(sK0),sK0) | ~v1_relat_1(k1_wellord2(sK0))),
% 1.35/0.55    inference(superposition,[],[f37,f83])).
% 1.35/0.55  fof(f83,plain,(
% 1.35/0.55    sK1(k1_wellord2(sK0),sK0) = sK2(k1_wellord2(sK0),sK0)),
% 1.35/0.55    inference(resolution,[],[f80,f28])).
% 1.35/0.55  fof(f80,plain,(
% 1.35/0.55    ( ! [X0] : (v4_relat_2(k1_wellord2(X0)) | sK1(k1_wellord2(X0),X0) = sK2(k1_wellord2(X0),X0)) )),
% 1.35/0.55    inference(resolution,[],[f79,f61])).
% 1.35/0.55  fof(f79,plain,(
% 1.35/0.55    ( ! [X0] : (r4_relat_2(k1_wellord2(X0),X0) | sK1(k1_wellord2(X0),X0) = sK2(k1_wellord2(X0),X0)) )),
% 1.35/0.55    inference(subsumption_resolution,[],[f78,f29])).
% 1.35/0.55  fof(f78,plain,(
% 1.35/0.55    ( ! [X0] : (r4_relat_2(k1_wellord2(X0),X0) | sK1(k1_wellord2(X0),X0) = sK2(k1_wellord2(X0),X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.35/0.55    inference(duplicate_literal_removal,[],[f77])).
% 1.35/0.55  fof(f77,plain,(
% 1.35/0.55    ( ! [X0] : (r4_relat_2(k1_wellord2(X0),X0) | sK1(k1_wellord2(X0),X0) = sK2(k1_wellord2(X0),X0) | r4_relat_2(k1_wellord2(X0),X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.35/0.55    inference(resolution,[],[f76,f33])).
% 1.35/0.55  fof(f33,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r4_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f20])).
% 1.35/0.55  fof(f20,plain,(
% 1.35/0.55    ! [X0] : (! [X1] : ((r4_relat_2(X0,X1) | (sK1(X0,X1) != sK2(X0,X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) & r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK1(X0,X1),X1))) & (! [X4,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~r4_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f18,f19])).
% 1.35/0.55  fof(f19,plain,(
% 1.35/0.55    ! [X1,X0] : (? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (sK1(X0,X1) != sK2(X0,X1) & r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) & r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) & r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK1(X0,X1),X1)))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f18,plain,(
% 1.35/0.55    ! [X0] : (! [X1] : ((r4_relat_2(X0,X1) | ? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~r4_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 1.35/0.55    inference(rectify,[],[f17])).
% 1.35/0.55  fof(f17,plain,(
% 1.35/0.55    ! [X0] : (! [X1] : ((r4_relat_2(X0,X1) | ? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~r4_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 1.35/0.55    inference(nnf_transformation,[],[f11])).
% 1.35/0.55  fof(f11,plain,(
% 1.35/0.55    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 1.35/0.55    inference(flattening,[],[f10])).
% 1.35/0.55  fof(f10,plain,(
% 1.35/0.55    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | (~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))) | ~v1_relat_1(X0))),
% 1.35/0.55    inference(ennf_transformation,[],[f4])).
% 1.35/0.55  fof(f4,axiom,(
% 1.35/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : ((r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => X2 = X3)))),
% 1.35/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).
% 1.35/0.55  fof(f76,plain,(
% 1.35/0.55    ( ! [X0] : (~r2_hidden(sK1(k1_wellord2(X0),X0),X0) | r4_relat_2(k1_wellord2(X0),X0) | sK1(k1_wellord2(X0),X0) = sK2(k1_wellord2(X0),X0)) )),
% 1.35/0.55    inference(subsumption_resolution,[],[f75,f29])).
% 1.35/0.55  fof(f75,plain,(
% 1.35/0.55    ( ! [X0] : (~r2_hidden(sK1(k1_wellord2(X0),X0),X0) | r4_relat_2(k1_wellord2(X0),X0) | sK1(k1_wellord2(X0),X0) = sK2(k1_wellord2(X0),X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.35/0.55    inference(duplicate_literal_removal,[],[f74])).
% 1.35/0.55  fof(f74,plain,(
% 1.35/0.55    ( ! [X0] : (~r2_hidden(sK1(k1_wellord2(X0),X0),X0) | r4_relat_2(k1_wellord2(X0),X0) | sK1(k1_wellord2(X0),X0) = sK2(k1_wellord2(X0),X0) | r4_relat_2(k1_wellord2(X0),X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.35/0.55    inference(resolution,[],[f73,f34])).
% 1.35/0.55  fof(f34,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r4_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f20])).
% 1.35/0.55  fof(f73,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~r2_hidden(sK2(k1_wellord2(X0),X1),X0) | ~r2_hidden(sK1(k1_wellord2(X0),X1),X0) | r4_relat_2(k1_wellord2(X0),X1) | sK1(k1_wellord2(X0),X1) = sK2(k1_wellord2(X0),X1)) )),
% 1.35/0.55    inference(subsumption_resolution,[],[f72,f69])).
% 1.35/0.55  fof(f69,plain,(
% 1.35/0.55    ( ! [X4,X3] : (r1_tarski(sK1(k1_wellord2(X3),X4),sK2(k1_wellord2(X3),X4)) | ~r2_hidden(sK1(k1_wellord2(X3),X4),X3) | ~r2_hidden(sK2(k1_wellord2(X3),X4),X3) | r4_relat_2(k1_wellord2(X3),X4)) )),
% 1.35/0.55    inference(subsumption_resolution,[],[f66,f29])).
% 1.35/0.55  fof(f66,plain,(
% 1.35/0.55    ( ! [X4,X3] : (~r2_hidden(sK1(k1_wellord2(X3),X4),X3) | r1_tarski(sK1(k1_wellord2(X3),X4),sK2(k1_wellord2(X3),X4)) | ~r2_hidden(sK2(k1_wellord2(X3),X4),X3) | r4_relat_2(k1_wellord2(X3),X4) | ~v1_relat_1(k1_wellord2(X3))) )),
% 1.35/0.55    inference(resolution,[],[f58,f35])).
% 1.35/0.55  fof(f35,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | r4_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f20])).
% 1.35/0.55  fof(f58,plain,(
% 1.35/0.55    ( ! [X4,X0,X5] : (~r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r2_hidden(X4,X0) | r1_tarski(X4,X5) | ~r2_hidden(X5,X0)) )),
% 1.35/0.55    inference(global_subsumption,[],[f29,f53])).
% 1.35/0.55  fof(f53,plain,(
% 1.35/0.55    ( ! [X4,X0,X5] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.35/0.55    inference(equality_resolution,[],[f39])).
% 1.35/0.55  fof(f39,plain,(
% 1.35/0.55    ( ! [X4,X0,X5,X1] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f25])).
% 1.35/0.55  fof(f72,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~r2_hidden(sK2(k1_wellord2(X0),X1),X0) | ~r2_hidden(sK1(k1_wellord2(X0),X1),X0) | r4_relat_2(k1_wellord2(X0),X1) | ~r1_tarski(sK1(k1_wellord2(X0),X1),sK2(k1_wellord2(X0),X1)) | sK1(k1_wellord2(X0),X1) = sK2(k1_wellord2(X0),X1)) )),
% 1.35/0.55    inference(resolution,[],[f70,f47])).
% 1.35/0.55  fof(f47,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.35/0.55    inference(cnf_transformation,[],[f27])).
% 1.35/0.55  fof(f27,plain,(
% 1.35/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.35/0.55    inference(flattening,[],[f26])).
% 1.35/0.55  fof(f26,plain,(
% 1.35/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.35/0.55    inference(nnf_transformation,[],[f1])).
% 1.35/0.55  fof(f1,axiom,(
% 1.35/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.35/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.35/0.55  fof(f70,plain,(
% 1.35/0.55    ( ! [X6,X5] : (r1_tarski(sK2(k1_wellord2(X5),X6),sK1(k1_wellord2(X5),X6)) | ~r2_hidden(sK2(k1_wellord2(X5),X6),X5) | ~r2_hidden(sK1(k1_wellord2(X5),X6),X5) | r4_relat_2(k1_wellord2(X5),X6)) )),
% 1.35/0.55    inference(subsumption_resolution,[],[f67,f29])).
% 1.35/0.55  fof(f67,plain,(
% 1.35/0.55    ( ! [X6,X5] : (~r2_hidden(sK2(k1_wellord2(X5),X6),X5) | r1_tarski(sK2(k1_wellord2(X5),X6),sK1(k1_wellord2(X5),X6)) | ~r2_hidden(sK1(k1_wellord2(X5),X6),X5) | r4_relat_2(k1_wellord2(X5),X6) | ~v1_relat_1(k1_wellord2(X5))) )),
% 1.35/0.55    inference(resolution,[],[f58,f36])).
% 1.35/0.55  fof(f36,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0) | r4_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f20])).
% 1.35/0.55  fof(f37,plain,(
% 1.35/0.55    ( ! [X0,X1] : (sK1(X0,X1) != sK2(X0,X1) | r4_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f20])).
% 1.35/0.55  % SZS output end Proof for theBenchmark
% 1.35/0.55  % (20377)------------------------------
% 1.35/0.55  % (20377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (20377)Termination reason: Refutation
% 1.35/0.55  
% 1.35/0.55  % (20377)Memory used [KB]: 6140
% 1.35/0.55  % (20377)Time elapsed: 0.126 s
% 1.35/0.55  % (20377)------------------------------
% 1.35/0.55  % (20377)------------------------------
% 1.35/0.55  % (20355)Success in time 0.186 s
%------------------------------------------------------------------------------
