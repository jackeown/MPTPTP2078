%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:59 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 280 expanded)
%              Number of leaves         :    9 (  63 expanded)
%              Depth                    :   19
%              Number of atoms          :  320 (1717 expanded)
%              Number of equality atoms :   28 ( 225 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(resolution,[],[f129,f28])).

fof(f28,plain,(
    ~ v8_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ~ v8_relat_2(k1_wellord2(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f17])).

fof(f17,plain,
    ( ? [X0] : ~ v8_relat_2(k1_wellord2(X0))
   => ~ v8_relat_2(k1_wellord2(sK0)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] : ~ v8_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_wellord2)).

fof(f129,plain,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(global_subsumption,[],[f69,f89,f109,f128])).

fof(f128,plain,(
    ! [X0] :
      ( r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0)))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f127,f89])).

fof(f127,plain,(
    ! [X0] :
      ( r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0)))
      | v8_relat_2(k1_wellord2(X0))
      | ~ r2_hidden(sK1(k1_wellord2(X0)),X0) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0] :
      ( r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0)))
      | v8_relat_2(k1_wellord2(X0))
      | ~ r2_hidden(sK1(k1_wellord2(X0)),X0)
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f113,f79])).

fof(f79,plain,(
    ! [X3] :
      ( r1_tarski(sK1(k1_wellord2(X3)),sK2(k1_wellord2(X3)))
      | ~ r2_hidden(sK1(k1_wellord2(X3)),X3)
      | v8_relat_2(k1_wellord2(X3)) ) ),
    inference(subsumption_resolution,[],[f78,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_wellord2(X0)),X0)
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f63,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f63,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_wellord2(X0)),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f56,f53])).

fof(f53,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f50,f29])).

fof(f50,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
              | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
            & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
              | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
            & r2_hidden(sK5(X0,X1),X0)
            & r2_hidden(sK4(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(nnf_transformation,[],[f12])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f56,plain,(
    ! [X1] :
      ( r2_hidden(sK2(X1),k3_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v8_relat_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,(
    ! [X1] :
      ( r2_hidden(sK2(X1),k3_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
            & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
            & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_hidden(k4_tarski(X1,X3),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(k4_tarski(X1,X2),X0) )
     => ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
        & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
        & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X4,X5,X6] :
              ( r2_hidden(k4_tarski(X4,X6),X0)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(k4_tarski(X4,X5),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v8_relat_2(X0)
          | ? [X1,X2,X3] :
              ( ~ r2_hidden(k4_tarski(X1,X3),X0)
              & r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) ) )
        & ( ! [X1,X2,X3] :
              ( r2_hidden(k4_tarski(X1,X3),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(k4_tarski(X1,X2),X0) )
          | ~ v8_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_wellord1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

% (986)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f78,plain,(
    ! [X3] :
      ( r1_tarski(sK1(k1_wellord2(X3)),sK2(k1_wellord2(X3)))
      | ~ r2_hidden(sK2(k1_wellord2(X3)),X3)
      | ~ r2_hidden(sK1(k1_wellord2(X3)),X3)
      | v8_relat_2(k1_wellord2(X3)) ) ),
    inference(subsumption_resolution,[],[f75,f29])).

fof(f75,plain,(
    ! [X3] :
      ( r1_tarski(sK1(k1_wellord2(X3)),sK2(k1_wellord2(X3)))
      | ~ r2_hidden(sK2(k1_wellord2(X3)),X3)
      | ~ r2_hidden(sK1(k1_wellord2(X3)),X3)
      | v8_relat_2(k1_wellord2(X3))
      | ~ v1_relat_1(k1_wellord2(X3)) ) ),
    inference(resolution,[],[f52,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f49,f29])).

fof(f49,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK2(k1_wellord2(X0)))
      | r1_tarski(X1,sK3(k1_wellord2(X0)))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f112,f109])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(k1_wellord2(X0)),X0)
      | v8_relat_2(k1_wellord2(X0))
      | r1_tarski(X1,sK3(k1_wellord2(X0)))
      | ~ r1_tarski(X1,sK2(k1_wellord2(X0))) ) ),
    inference(resolution,[],[f81,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f81,plain,(
    ! [X4] :
      ( r1_tarski(sK2(k1_wellord2(X4)),sK3(k1_wellord2(X4)))
      | ~ r2_hidden(sK3(k1_wellord2(X4)),X4)
      | v8_relat_2(k1_wellord2(X4)) ) ),
    inference(subsumption_resolution,[],[f80,f64])).

fof(f80,plain,(
    ! [X4] :
      ( r1_tarski(sK2(k1_wellord2(X4)),sK3(k1_wellord2(X4)))
      | ~ r2_hidden(sK3(k1_wellord2(X4)),X4)
      | ~ r2_hidden(sK2(k1_wellord2(X4)),X4)
      | v8_relat_2(k1_wellord2(X4)) ) ),
    inference(subsumption_resolution,[],[f76,f29])).

fof(f76,plain,(
    ! [X4] :
      ( r1_tarski(sK2(k1_wellord2(X4)),sK3(k1_wellord2(X4)))
      | ~ r2_hidden(sK3(k1_wellord2(X4)),X4)
      | ~ r2_hidden(sK2(k1_wellord2(X4)),X4)
      | v8_relat_2(k1_wellord2(X4))
      | ~ v1_relat_1(k1_wellord2(X4)) ) ),
    inference(resolution,[],[f52,f32])).

fof(f109,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k1_wellord2(X0)),X0)
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f108,f29])).

fof(f108,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k1_wellord2(X0)),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f60,f53])).

fof(f60,plain,(
    ! [X1] :
      ( r2_hidden(sK3(X1),k3_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v8_relat_2(X1) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X1] :
      ( r2_hidden(sK3(X1),k3_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f42,f32])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f89,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k1_wellord2(X0)),X0)
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f88,f29])).

fof(f88,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k1_wellord2(X0)),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f57,f53])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v8_relat_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f41,f31])).

fof(f69,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0)))
      | ~ r2_hidden(sK3(k1_wellord2(X0)),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0)),X0)
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f66,f29])).

fof(f66,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0)))
      | ~ r2_hidden(sK3(k1_wellord2(X0)),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0)),X0)
      | v8_relat_2(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f51,f33])).

% (980)Refutation not found, incomplete strategy% (980)------------------------------
% (980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f33,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
      | v8_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

% (980)Termination reason: Refutation not found, incomplete strategy

fof(f51,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f48,f29])).

% (980)Memory used [KB]: 10618
% (980)Time elapsed: 0.073 s
% (980)------------------------------
% (980)------------------------------
fof(f48,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:34:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.42  % (971)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.42  % (971)Refutation not found, incomplete strategy% (971)------------------------------
% 0.19/0.42  % (971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (971)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.42  
% 0.19/0.42  % (971)Memory used [KB]: 10618
% 0.19/0.42  % (971)Time elapsed: 0.044 s
% 0.19/0.42  % (971)------------------------------
% 0.19/0.42  % (971)------------------------------
% 0.19/0.44  % (977)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.45  % (975)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.45  % (980)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.45  % (970)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.46  % (974)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.46  % (968)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.46  % (969)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.46  % (970)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % (968)Refutation not found, incomplete strategy% (968)------------------------------
% 0.19/0.46  % (968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (968)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (968)Memory used [KB]: 6140
% 0.19/0.46  % (968)Time elapsed: 0.075 s
% 0.19/0.46  % (968)------------------------------
% 0.19/0.46  % (968)------------------------------
% 0.19/0.47  % (969)Refutation not found, incomplete strategy% (969)------------------------------
% 0.19/0.47  % (969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (969)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (969)Memory used [KB]: 10490
% 0.19/0.47  % (969)Time elapsed: 0.063 s
% 0.19/0.47  % (969)------------------------------
% 0.19/0.47  % (969)------------------------------
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f166,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(resolution,[],[f129,f28])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    ~v8_relat_2(k1_wellord2(sK0))),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ~v8_relat_2(k1_wellord2(sK0))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ? [X0] : ~v8_relat_2(k1_wellord2(X0)) => ~v8_relat_2(k1_wellord2(sK0))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f8,plain,(
% 0.19/0.47    ? [X0] : ~v8_relat_2(k1_wellord2(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,negated_conjecture,(
% 0.19/0.47    ~! [X0] : v8_relat_2(k1_wellord2(X0))),
% 0.19/0.47    inference(negated_conjecture,[],[f6])).
% 0.19/0.47  fof(f6,conjecture,(
% 0.19/0.47    ! [X0] : v8_relat_2(k1_wellord2(X0))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_wellord2)).
% 0.19/0.47  fof(f129,plain,(
% 0.19/0.47    ( ! [X0] : (v8_relat_2(k1_wellord2(X0))) )),
% 0.19/0.47    inference(global_subsumption,[],[f69,f89,f109,f128])).
% 0.19/0.47  fof(f128,plain,(
% 0.19/0.47    ( ! [X0] : (r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))) | v8_relat_2(k1_wellord2(X0))) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f127,f89])).
% 0.19/0.47  fof(f127,plain,(
% 0.19/0.47    ( ! [X0] : (r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))) | v8_relat_2(k1_wellord2(X0)) | ~r2_hidden(sK1(k1_wellord2(X0)),X0)) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f126])).
% 0.19/0.47  fof(f126,plain,(
% 0.19/0.47    ( ! [X0] : (r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))) | v8_relat_2(k1_wellord2(X0)) | ~r2_hidden(sK1(k1_wellord2(X0)),X0) | v8_relat_2(k1_wellord2(X0))) )),
% 0.19/0.47    inference(resolution,[],[f113,f79])).
% 0.19/0.47  fof(f79,plain,(
% 0.19/0.47    ( ! [X3] : (r1_tarski(sK1(k1_wellord2(X3)),sK2(k1_wellord2(X3))) | ~r2_hidden(sK1(k1_wellord2(X3)),X3) | v8_relat_2(k1_wellord2(X3))) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f78,f64])).
% 0.19/0.47  fof(f64,plain,(
% 0.19/0.47    ( ! [X0] : (r2_hidden(sK2(k1_wellord2(X0)),X0) | v8_relat_2(k1_wellord2(X0))) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f63,f29])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.19/0.47  fof(f63,plain,(
% 0.19/0.47    ( ! [X0] : (r2_hidden(sK2(k1_wellord2(X0)),X0) | ~v1_relat_1(k1_wellord2(X0)) | v8_relat_2(k1_wellord2(X0))) )),
% 0.19/0.47    inference(superposition,[],[f56,f53])).
% 0.19/0.47  fof(f53,plain,(
% 0.19/0.47    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f50,f29])).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.19/0.47    inference(equality_resolution,[],[f34])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1)) & r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),X0)))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(rectify,[],[f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(nnf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,plain,(
% 0.19/0.47    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(flattening,[],[f11])).
% 0.19/0.47  fof(f11,plain,(
% 0.19/0.47    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.19/0.47  fof(f56,plain,(
% 0.19/0.47    ( ! [X1] : (r2_hidden(sK2(X1),k3_relat_1(X1)) | ~v1_relat_1(X1) | v8_relat_2(X1)) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f55])).
% 0.19/0.47  fof(f55,plain,(
% 0.19/0.47    ( ! [X1] : (r2_hidden(sK2(X1),k3_relat_1(X1)) | ~v1_relat_1(X1) | v8_relat_2(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(resolution,[],[f41,f32])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    ( ! [X0] : (r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0] : (((v8_relat_2(X0) | (~r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f20,f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0] : (? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => (~r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) & r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X4,X5,X6] : (r2_hidden(k4_tarski(X4,X6),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(rectify,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0] : (((v8_relat_2(X0) | ? [X1,X2,X3] : (~r2_hidden(k4_tarski(X1,X3),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0))) & (! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)) | ~v8_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(nnf_transformation,[],[f10])).
% 0.19/0.47  fof(f10,plain,(
% 0.19/0.47    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(flattening,[],[f9])).
% 0.19/0.47  fof(f9,plain,(
% 0.19/0.47    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | (~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => r2_hidden(k4_tarski(X1,X3),X0))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_wellord1)).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X0,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.19/0.47    inference(flattening,[],[f13])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.19/0.47    inference(ennf_transformation,[],[f2])).
% 0.19/0.47  % (986)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 0.19/0.47  fof(f78,plain,(
% 0.19/0.47    ( ! [X3] : (r1_tarski(sK1(k1_wellord2(X3)),sK2(k1_wellord2(X3))) | ~r2_hidden(sK2(k1_wellord2(X3)),X3) | ~r2_hidden(sK1(k1_wellord2(X3)),X3) | v8_relat_2(k1_wellord2(X3))) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f75,f29])).
% 0.19/0.47  fof(f75,plain,(
% 0.19/0.47    ( ! [X3] : (r1_tarski(sK1(k1_wellord2(X3)),sK2(k1_wellord2(X3))) | ~r2_hidden(sK2(k1_wellord2(X3)),X3) | ~r2_hidden(sK1(k1_wellord2(X3)),X3) | v8_relat_2(k1_wellord2(X3)) | ~v1_relat_1(k1_wellord2(X3))) )),
% 0.19/0.47    inference(resolution,[],[f52,f31])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ( ! [X0] : (r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f22])).
% 0.19/0.47  fof(f52,plain,(
% 0.19/0.47    ( ! [X4,X0,X5] : (~r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f49,f29])).
% 0.19/0.47  fof(f49,plain,(
% 0.19/0.47    ( ! [X4,X0,X5] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.19/0.47    inference(equality_resolution,[],[f35])).
% 0.19/0.47  fof(f35,plain,(
% 0.19/0.47    ( ! [X4,X0,X5,X1] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  fof(f113,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r1_tarski(X1,sK2(k1_wellord2(X0))) | r1_tarski(X1,sK3(k1_wellord2(X0))) | v8_relat_2(k1_wellord2(X0))) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f112,f109])).
% 0.19/0.47  fof(f112,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r2_hidden(sK3(k1_wellord2(X0)),X0) | v8_relat_2(k1_wellord2(X0)) | r1_tarski(X1,sK3(k1_wellord2(X0))) | ~r1_tarski(X1,sK2(k1_wellord2(X0)))) )),
% 0.19/0.47    inference(resolution,[],[f81,f43])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f16])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.47    inference(flattening,[],[f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.47    inference(ennf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.19/0.47  fof(f81,plain,(
% 0.19/0.47    ( ! [X4] : (r1_tarski(sK2(k1_wellord2(X4)),sK3(k1_wellord2(X4))) | ~r2_hidden(sK3(k1_wellord2(X4)),X4) | v8_relat_2(k1_wellord2(X4))) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f80,f64])).
% 0.19/0.47  fof(f80,plain,(
% 0.19/0.47    ( ! [X4] : (r1_tarski(sK2(k1_wellord2(X4)),sK3(k1_wellord2(X4))) | ~r2_hidden(sK3(k1_wellord2(X4)),X4) | ~r2_hidden(sK2(k1_wellord2(X4)),X4) | v8_relat_2(k1_wellord2(X4))) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f76,f29])).
% 0.19/0.47  fof(f76,plain,(
% 0.19/0.47    ( ! [X4] : (r1_tarski(sK2(k1_wellord2(X4)),sK3(k1_wellord2(X4))) | ~r2_hidden(sK3(k1_wellord2(X4)),X4) | ~r2_hidden(sK2(k1_wellord2(X4)),X4) | v8_relat_2(k1_wellord2(X4)) | ~v1_relat_1(k1_wellord2(X4))) )),
% 0.19/0.47    inference(resolution,[],[f52,f32])).
% 0.19/0.47  fof(f109,plain,(
% 0.19/0.47    ( ! [X0] : (r2_hidden(sK3(k1_wellord2(X0)),X0) | v8_relat_2(k1_wellord2(X0))) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f108,f29])).
% 0.19/0.47  fof(f108,plain,(
% 0.19/0.47    ( ! [X0] : (r2_hidden(sK3(k1_wellord2(X0)),X0) | ~v1_relat_1(k1_wellord2(X0)) | v8_relat_2(k1_wellord2(X0))) )),
% 0.19/0.47    inference(superposition,[],[f60,f53])).
% 0.19/0.47  fof(f60,plain,(
% 0.19/0.47    ( ! [X1] : (r2_hidden(sK3(X1),k3_relat_1(X1)) | ~v1_relat_1(X1) | v8_relat_2(X1)) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f59])).
% 0.19/0.47  fof(f59,plain,(
% 0.19/0.47    ( ! [X1] : (r2_hidden(sK3(X1),k3_relat_1(X1)) | ~v1_relat_1(X1) | v8_relat_2(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(resolution,[],[f42,f32])).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f14])).
% 0.19/0.47  fof(f89,plain,(
% 0.19/0.47    ( ! [X0] : (r2_hidden(sK1(k1_wellord2(X0)),X0) | v8_relat_2(k1_wellord2(X0))) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f88,f29])).
% 0.19/0.47  fof(f88,plain,(
% 0.19/0.47    ( ! [X0] : (r2_hidden(sK1(k1_wellord2(X0)),X0) | ~v1_relat_1(k1_wellord2(X0)) | v8_relat_2(k1_wellord2(X0))) )),
% 0.19/0.47    inference(superposition,[],[f57,f53])).
% 0.19/0.47  fof(f57,plain,(
% 0.19/0.47    ( ! [X0] : (r2_hidden(sK1(X0),k3_relat_1(X0)) | ~v1_relat_1(X0) | v8_relat_2(X0)) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f54])).
% 0.19/0.47  fof(f54,plain,(
% 0.19/0.47    ( ! [X0] : (r2_hidden(sK1(X0),k3_relat_1(X0)) | ~v1_relat_1(X0) | v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.47    inference(resolution,[],[f41,f31])).
% 0.19/0.47  fof(f69,plain,(
% 0.19/0.47    ( ! [X0] : (~r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))) | ~r2_hidden(sK3(k1_wellord2(X0)),X0) | ~r2_hidden(sK1(k1_wellord2(X0)),X0) | v8_relat_2(k1_wellord2(X0))) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f66,f29])).
% 0.19/0.47  fof(f66,plain,(
% 0.19/0.47    ( ! [X0] : (~r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))) | ~r2_hidden(sK3(k1_wellord2(X0)),X0) | ~r2_hidden(sK1(k1_wellord2(X0)),X0) | v8_relat_2(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.19/0.47    inference(resolution,[],[f51,f33])).
% 0.19/0.47  % (980)Refutation not found, incomplete strategy% (980)------------------------------
% 0.19/0.47  % (980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ( ! [X0] : (~r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0) | v8_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f22])).
% 0.19/0.47  % (980)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  fof(f51,plain,(
% 0.19/0.47    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f48,f29])).
% 0.19/0.47  % (980)Memory used [KB]: 10618
% 0.19/0.47  % (980)Time elapsed: 0.073 s
% 0.19/0.47  % (980)------------------------------
% 0.19/0.47  % (980)------------------------------
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.19/0.47    inference(equality_resolution,[],[f36])).
% 0.19/0.47  fof(f36,plain,(
% 0.19/0.47    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f27])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (970)------------------------------
% 0.19/0.47  % (970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (970)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (970)Memory used [KB]: 10618
% 0.19/0.47  % (970)Time elapsed: 0.065 s
% 0.19/0.47  % (970)------------------------------
% 0.19/0.47  % (970)------------------------------
% 0.19/0.47  % (959)Success in time 0.13 s
%------------------------------------------------------------------------------
