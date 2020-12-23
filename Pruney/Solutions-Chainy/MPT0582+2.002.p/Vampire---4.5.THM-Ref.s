%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 153 expanded)
%              Number of leaves         :    9 (  44 expanded)
%              Depth                    :   19
%              Number of atoms          :  272 ( 856 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f407,plain,(
    $false ),
    inference(subsumption_resolution,[],[f406,f33])).

fof(f33,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
    & r1_tarski(sK2,sK1)
    & r1_tarski(k1_relat_1(sK2),sK0)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
            & r1_tarski(X2,X1)
            & r1_tarski(k1_relat_1(X2),X0)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
          & r1_tarski(X2,sK1)
          & r1_tarski(k1_relat_1(X2),sK0)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,k7_relat_1(sK1,sK0))
        & r1_tarski(X2,sK1)
        & r1_tarski(k1_relat_1(X2),sK0)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK2,k7_relat_1(sK1,sK0))
      & r1_tarski(sK2,sK1)
      & r1_tarski(k1_relat_1(sK2),sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & r1_tarski(k1_relat_1(X2),X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k7_relat_1(X1,X0))
          & r1_tarski(X2,X1)
          & r1_tarski(k1_relat_1(X2),X0)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( ( r1_tarski(X2,X1)
                & r1_tarski(k1_relat_1(X2),X0) )
             => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k1_relat_1(X2),X0) )
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).

fof(f406,plain,(
    ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f396,f36])).

fof(f36,plain,(
    ~ r1_tarski(sK2,k7_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f396,plain,
    ( r1_tarski(sK2,k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f392])).

fof(f392,plain,
    ( r1_tarski(sK2,k7_relat_1(sK1,sK0))
    | r1_tarski(sK2,k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f376,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f376,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK3(sK2,X0),sK4(sK2,X0)),k7_relat_1(sK1,sK0))
      | r1_tarski(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f373,f32])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f373,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK3(sK2,X0),sK4(sK2,X0)),k7_relat_1(sK1,sK0))
      | r1_tarski(sK2,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f371,f35])).

fof(f35,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f371,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2,X0)
      | r2_hidden(k4_tarski(sK3(sK2,X1),sK4(sK2,X1)),k7_relat_1(X0,sK0))
      | r1_tarski(sK2,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f364])).

fof(f364,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2,X0)
      | r2_hidden(k4_tarski(sK3(sK2,X1),sK4(sK2,X1)),k7_relat_1(X0,sK0))
      | r1_tarski(sK2,X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(sK2,X1) ) ),
    inference(resolution,[],[f129,f76])).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK2,X0),sK0)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f59,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f66,f33])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK2) ) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | r2_hidden(X0,sK0)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f53,f61])).

fof(f61,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f60,f33])).

fof(f60,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f34,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f34,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)
                  | ~ r2_hidden(sK5(X0,X1,X2),X1)
                  | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)
                    & r2_hidden(sK5(X0,X1,X2),X1) )
                  | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0)
            & r2_hidden(sK5(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X0)
                    | ~ r2_hidden(X5,X1) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                      & r2_hidden(X5,X1) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k7_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X0)
                    | ~ r2_hidden(X3,X1) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                      & r2_hidden(X3,X1) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k7_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

fof(f59,plain,(
    ! [X4] :
      ( r2_hidden(k4_tarski(sK3(sK2,X4),sK4(sK2,X4)),sK2)
      | r1_tarski(sK2,X4) ) ),
    inference(resolution,[],[f33,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f129,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(sK3(sK2,X1),X3)
      | ~ r1_tarski(sK2,X2)
      | r2_hidden(k4_tarski(sK3(sK2,X1),sK4(sK2,X1)),k7_relat_1(X2,X3))
      | r1_tarski(sK2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f122,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f122,plain,(
    ! [X2,X3,X1] :
      ( r1_tarski(sK2,X1)
      | ~ r1_tarski(sK2,X2)
      | r2_hidden(k4_tarski(sK3(sK2,X1),sK4(sK2,X1)),k7_relat_1(X2,X3))
      | ~ r2_hidden(sK3(sK2,X1),X3)
      | ~ v1_relat_1(k7_relat_1(X2,X3))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f84,f51])).

fof(f51,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1))
      | ~ r2_hidden(X5,X1)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X2)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X5,X1)
      | k7_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    ! [X4,X3] :
      ( r2_hidden(k4_tarski(sK3(sK2,X3),sK4(sK2,X3)),X4)
      | r1_tarski(sK2,X3)
      | ~ r1_tarski(sK2,X4) ) ),
    inference(subsumption_resolution,[],[f79,f33])).

fof(f79,plain,(
    ! [X4,X3] :
      ( r1_tarski(sK2,X3)
      | r2_hidden(k4_tarski(sK3(sK2,X3),sK4(sK2,X3)),X4)
      | ~ r1_tarski(sK2,X4)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f59,f37])).

fof(f37,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X5),X0)
      | r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:32:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (24271)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (24287)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (24279)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (24265)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (24270)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (24283)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (24278)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (24272)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (24276)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (24268)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (24285)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (24271)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (24289)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (24280)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (24290)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (24275)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (24264)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (24269)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (24267)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (24286)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (24274)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (24263)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (24281)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (24282)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (24288)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (24284)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (24277)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (24291)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f407,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f406,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    v1_relat_1(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    (~r1_tarski(sK2,k7_relat_1(sK1,sK0)) & r1_tarski(sK2,sK1) & r1_tarski(k1_relat_1(sK2),sK0) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f17,f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(X2,k7_relat_1(sK1,sK0)) & r1_tarski(X2,sK1) & r1_tarski(k1_relat_1(X2),sK0) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ? [X2] : (~r1_tarski(X2,k7_relat_1(sK1,sK0)) & r1_tarski(X2,sK1) & r1_tarski(k1_relat_1(X2),sK0) & v1_relat_1(X2)) => (~r1_tarski(sK2,k7_relat_1(sK1,sK0)) & r1_tarski(sK2,sK1) & r1_tarski(k1_relat_1(sK2),sK0) & v1_relat_1(sK2))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f9,plain,(
% 0.21/0.56    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,k7_relat_1(X1,X0)) & r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.56    inference(flattening,[],[f8])).
% 0.21/0.56  fof(f8,plain,(
% 0.21/0.56    ? [X0,X1] : (? [X2] : ((~r1_tarski(X2,k7_relat_1(X1,X0)) & (r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0)) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.21/0.56    inference(negated_conjecture,[],[f6])).
% 0.21/0.56  fof(f6,conjecture,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r1_tarski(X2,X1) & r1_tarski(k1_relat_1(X2),X0)) => r1_tarski(X2,k7_relat_1(X1,X0)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).
% 0.21/0.56  fof(f406,plain,(
% 0.21/0.56    ~v1_relat_1(sK2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f396,f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ~r1_tarski(sK2,k7_relat_1(sK1,sK0))),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f396,plain,(
% 0.21/0.56    r1_tarski(sK2,k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK2)),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f392])).
% 0.21/0.56  fof(f392,plain,(
% 0.21/0.56    r1_tarski(sK2,k7_relat_1(sK1,sK0)) | r1_tarski(sK2,k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK2)),
% 0.21/0.56    inference(resolution,[],[f376,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) | r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f20,f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0)) => (~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X4,X5] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(k4_tarski(X4,X5),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(rectify,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((r1_tarski(X0,X1) | ? [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),X1) & r2_hidden(k4_tarski(X2,X3),X0))) & (! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0)) | ~r1_tarski(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 0.21/0.56  fof(f376,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK3(sK2,X0),sK4(sK2,X0)),k7_relat_1(sK1,sK0)) | r1_tarski(sK2,X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f373,f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    v1_relat_1(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f373,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k4_tarski(sK3(sK2,X0),sK4(sK2,X0)),k7_relat_1(sK1,sK0)) | r1_tarski(sK2,X0) | ~v1_relat_1(sK1)) )),
% 0.21/0.56    inference(resolution,[],[f371,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    r1_tarski(sK2,sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f371,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(sK2,X0) | r2_hidden(k4_tarski(sK3(sK2,X1),sK4(sK2,X1)),k7_relat_1(X0,sK0)) | r1_tarski(sK2,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f364])).
% 0.21/0.56  fof(f364,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(sK2,X0) | r2_hidden(k4_tarski(sK3(sK2,X1),sK4(sK2,X1)),k7_relat_1(X0,sK0)) | r1_tarski(sK2,X1) | ~v1_relat_1(X0) | r1_tarski(sK2,X1)) )),
% 0.21/0.56    inference(resolution,[],[f129,f76])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK3(sK2,X0),sK0) | r1_tarski(sK2,X0)) )),
% 0.21/0.56    inference(resolution,[],[f59,f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X0,sK0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f66,f33])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X0,sK0) | ~v1_relat_1(sK2)) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | r2_hidden(X0,sK0) | ~v1_relat_1(sK2) | ~v1_relat_1(sK2)) )),
% 0.21/0.56    inference(superposition,[],[f53,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    sK2 = k7_relat_1(sK2,sK0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f60,f33])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.21/0.56    inference(resolution,[],[f34,f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(flattening,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X6,X0,X5,X1] : (~r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X2) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f25,f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X2,X1,X0] : (? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) | ~r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X0) & r2_hidden(sK5(X0,X1,X2),X1)) | r2_hidden(k4_tarski(sK5(X0,X1,X2),sK6(X0,X1,X2)),X2))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X5,X6] : ((r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1)) & ((r2_hidden(k4_tarski(X5,X6),X0) & r2_hidden(X5,X1)) | ~r2_hidden(k4_tarski(X5,X6),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(rectify,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : ((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(flattening,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : (((k7_relat_1(X0,X1) = X2 | ? [X3,X4] : (((~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X3,X1))) & ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k7_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X4] : (r2_hidden(k4_tarski(sK3(sK2,X4),sK4(sK2,X4)),sK2) | r1_tarski(sK2,X4)) )),
% 0.21/0.56    inference(resolution,[],[f33,f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f129,plain,(
% 0.21/0.56    ( ! [X2,X3,X1] : (~r2_hidden(sK3(sK2,X1),X3) | ~r1_tarski(sK2,X2) | r2_hidden(k4_tarski(sK3(sK2,X1),sK4(sK2,X1)),k7_relat_1(X2,X3)) | r1_tarski(sK2,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f122,f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    ( ! [X2,X3,X1] : (r1_tarski(sK2,X1) | ~r1_tarski(sK2,X2) | r2_hidden(k4_tarski(sK3(sK2,X1),sK4(sK2,X1)),k7_relat_1(X2,X3)) | ~r2_hidden(sK3(sK2,X1),X3) | ~v1_relat_1(k7_relat_1(X2,X3)) | ~v1_relat_1(X2)) )),
% 0.21/0.56    inference(resolution,[],[f84,f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X6,X0,X5,X1] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(k4_tarski(X5,X6),k7_relat_1(X0,X1)) | ~r2_hidden(X5,X1) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(equality_resolution,[],[f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ( ! [X6,X2,X0,X5,X1] : (r2_hidden(k4_tarski(X5,X6),X2) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X5,X1) | k7_relat_1(X0,X1) != X2 | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    ( ! [X4,X3] : (r2_hidden(k4_tarski(sK3(sK2,X3),sK4(sK2,X3)),X4) | r1_tarski(sK2,X3) | ~r1_tarski(sK2,X4)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f79,f33])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    ( ! [X4,X3] : (r1_tarski(sK2,X3) | r2_hidden(k4_tarski(sK3(sK2,X3),sK4(sK2,X3)),X4) | ~r1_tarski(sK2,X4) | ~v1_relat_1(sK2)) )),
% 0.21/0.56    inference(resolution,[],[f59,f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X4,X0,X5,X1] : (~r2_hidden(k4_tarski(X4,X5),X0) | r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (24271)------------------------------
% 0.21/0.56  % (24271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24271)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (24271)Memory used [KB]: 11001
% 0.21/0.56  % (24271)Time elapsed: 0.114 s
% 0.21/0.56  % (24271)------------------------------
% 0.21/0.56  % (24271)------------------------------
% 1.50/0.56  % (24292)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.50/0.56  % (24262)Success in time 0.191 s
%------------------------------------------------------------------------------
