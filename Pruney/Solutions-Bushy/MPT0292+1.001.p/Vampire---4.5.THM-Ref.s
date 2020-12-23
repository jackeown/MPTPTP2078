%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0292+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:42 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 263 expanded)
%              Number of leaves         :   10 (  84 expanded)
%              Depth                    :   15
%              Number of atoms          :  195 (1303 expanded)
%              Number of equality atoms :   29 ( 208 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(subsumption_resolution,[],[f158,f157])).

fof(f157,plain,(
    r2_hidden(sK5(sK0,sK0),sK0) ),
    inference(resolution,[],[f153,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f153,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f151,f41])).

fof(f41,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f151,plain,(
    ~ r2_hidden(sK0,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f150,f141])).

fof(f141,plain,(
    r2_hidden(sK1(k1_zfmisc_1(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f140,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | r2_hidden(sK1(k1_zfmisc_1(sK0),sK0),sK0)
      | ~ r2_hidden(X0,sK2(k1_zfmisc_1(sK0),sK0)) ) ),
    inference(resolution,[],[f55,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,
    ( r1_tarski(sK2(k1_zfmisc_1(sK0),sK0),sK0)
    | r2_hidden(sK1(k1_zfmisc_1(sK0),sK0),sK0) ),
    inference(resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,
    ( r2_hidden(sK2(k1_zfmisc_1(sK0),sK0),k1_zfmisc_1(sK0))
    | r2_hidden(sK1(k1_zfmisc_1(sK0),sK0),sK0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X1] :
      ( sK0 != X1
      | r2_hidden(sK2(k1_zfmisc_1(sK0),X1),k1_zfmisc_1(sK0))
      | r2_hidden(sK1(k1_zfmisc_1(sK0),X1),X1) ) ),
    inference(superposition,[],[f24,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f11,f14,f13,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK1(X0,X1),X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK1(X0,X1),sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f24,plain,(
    sK0 != k3_tarski(k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    sK0 != k3_tarski(k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f8])).

fof(f8,plain,
    ( ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0
   => sK0 != k3_tarski(k1_zfmisc_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] : k3_tarski(k1_zfmisc_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f140,plain,
    ( r2_hidden(sK1(k1_zfmisc_1(sK0),sK0),sK2(k1_zfmisc_1(sK0),sK0))
    | r2_hidden(sK1(k1_zfmisc_1(sK0),sK0),sK0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( sK0 != X0
      | r2_hidden(sK1(k1_zfmisc_1(sK0),X0),sK2(k1_zfmisc_1(sK0),X0))
      | r2_hidden(sK1(k1_zfmisc_1(sK0),X0),X0) ) ),
    inference(superposition,[],[f24,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK1(X0,X1),sK2(X0,X1))
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f150,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK1(k1_zfmisc_1(sK0),sK0),sK0) ),
    inference(subsumption_resolution,[],[f142,f24])).

fof(f142,plain,
    ( sK0 = k3_tarski(k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK1(k1_zfmisc_1(sK0),sK0),sK0) ),
    inference(resolution,[],[f141,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( k3_tarski(X0) = X1
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK1(X0,X1),X3)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f158,plain,(
    ~ r2_hidden(sK5(sK0,sK0),sK0) ),
    inference(resolution,[],[f153,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
