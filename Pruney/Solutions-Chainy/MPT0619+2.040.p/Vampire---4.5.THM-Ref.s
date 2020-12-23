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
% DateTime   : Thu Dec  3 12:51:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 702 expanded)
%              Number of leaves         :   10 ( 186 expanded)
%              Depth                    :   27
%              Number of atoms          :  312 (3475 expanded)
%              Number of equality atoms :  133 (1554 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(subsumption_resolution,[],[f244,f48])).

fof(f48,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f244,plain,(
    ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(trivial_inequality_removal,[],[f242])).

fof(f242,plain,
    ( sK5(sK1) != sK5(sK1)
    | ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(superposition,[],[f236,f86])).

fof(f86,plain,(
    k1_funct_1(sK1,sK0) = sK5(sK1) ),
    inference(backward_demodulation,[],[f75,f85])).

fof(f85,plain,(
    sK0 = sK4(sK1,sK5(sK1)) ),
    inference(resolution,[],[f73,f49])).

fof(f49,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,(
    r2_hidden(sK4(sK1,sK5(sK1)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f72,f29])).

fof(f29,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
    & k1_tarski(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))
      & k1_tarski(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f72,plain,(
    r2_hidden(sK4(sK1,sK5(sK1)),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f71,f27])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,
    ( r2_hidden(sK4(sK1,sK5(sK1)),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f69,f28])).

fof(f28,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,
    ( r2_hidden(sK4(sK1,sK5(sK1)),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f61,f46])).

fof(f46,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f19,f18,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK2(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f61,plain,(
    r2_hidden(sK5(sK1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f57,f48])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(sK5(sK1),k2_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f55,f27])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | r2_hidden(sK5(sK1),k2_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f37,f29])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | r2_hidden(sK5(X1),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f21])).

fof(f21,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
     => r2_hidden(sK5(X1),k2_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

fof(f75,plain,(
    sK5(sK1) = k1_funct_1(sK1,sK4(sK1,sK5(sK1))) ),
    inference(subsumption_resolution,[],[f74,f27])).

fof(f74,plain,
    ( sK5(sK1) = k1_funct_1(sK1,sK4(sK1,sK5(sK1)))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f70,f28])).

fof(f70,plain,
    ( sK5(sK1) = k1_funct_1(sK1,sK4(sK1,sK5(sK1)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f61,f45])).

fof(f45,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f236,plain,(
    ! [X0] :
      ( sK5(sK1) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,k1_tarski(sK0)) ) ),
    inference(forward_demodulation,[],[f235,f29])).

fof(f235,plain,(
    ! [X0] :
      ( sK5(sK1) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f234,f27])).

% (19322)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f234,plain,(
    ! [X0] :
      ( sK5(sK1) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f233,f28])).

fof(f233,plain,(
    ! [X0] :
      ( sK5(sK1) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f232,f48])).

fof(f232,plain,(
    ! [X0] :
      ( sK5(sK1) != k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(sK5(sK1),k1_tarski(sK5(sK1)))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f231,f88])).

fof(f88,plain,(
    k2_relat_1(sK1) != k1_tarski(sK5(sK1)) ),
    inference(backward_demodulation,[],[f30,f86])).

fof(f30,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f231,plain,(
    ! [X0] :
      ( sK5(sK1) != k1_funct_1(sK1,X0)
      | k2_relat_1(sK1) = k1_tarski(sK5(sK1))
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | ~ r2_hidden(sK5(sK1),k1_tarski(sK5(sK1)))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f36,f224])).

fof(f224,plain,(
    sK5(sK1) = sK2(sK1,k1_tarski(sK5(sK1))) ),
    inference(subsumption_resolution,[],[f223,f88])).

fof(f223,plain,
    ( sK5(sK1) = sK2(sK1,k1_tarski(sK5(sK1)))
    | k2_relat_1(sK1) = k1_tarski(sK5(sK1)) ),
    inference(equality_resolution,[],[f202])).

fof(f202,plain,(
    ! [X0] :
      ( sK5(sK1) != X0
      | sK2(sK1,k1_tarski(X0)) = X0
      | k1_tarski(X0) = k2_relat_1(sK1) ) ),
    inference(equality_factoring,[],[f159])).

fof(f159,plain,(
    ! [X0] :
      ( sK5(sK1) = sK2(sK1,k1_tarski(X0))
      | sK2(sK1,k1_tarski(X0)) = X0
      | k1_tarski(X0) = k2_relat_1(sK1) ) ),
    inference(forward_demodulation,[],[f158,f86])).

fof(f158,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = sK2(sK1,k1_tarski(X0))
      | k1_tarski(X0) = k2_relat_1(sK1)
      | sK2(sK1,k1_tarski(X0)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK0) = sK2(sK1,k1_tarski(X0))
      | k1_tarski(X0) = k2_relat_1(sK1)
      | sK2(sK1,k1_tarski(X0)) = X0
      | k1_tarski(X0) = k2_relat_1(sK1)
      | sK2(sK1,k1_tarski(X0)) = X0 ) ),
    inference(superposition,[],[f94,f112])).

fof(f112,plain,(
    ! [X4] :
      ( sK0 = sK3(sK1,k1_tarski(X4))
      | k2_relat_1(sK1) = k1_tarski(X4)
      | sK2(sK1,k1_tarski(X4)) = X4 ) ),
    inference(resolution,[],[f77,f49])).

fof(f77,plain,(
    ! [X1] :
      ( r2_hidden(sK2(sK1,X1),X1)
      | k2_relat_1(sK1) = X1
      | sK0 = sK3(sK1,X1) ) ),
    inference(resolution,[],[f53,f49])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0),k1_tarski(sK0))
      | r2_hidden(sK2(sK1,X0),X0)
      | k2_relat_1(sK1) = X0 ) ),
    inference(forward_demodulation,[],[f52,f29])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0),k1_relat_1(sK1))
      | r2_hidden(sK2(sK1,X0),X0)
      | k2_relat_1(sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f50,f27])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0),k1_relat_1(sK1))
      | r2_hidden(sK2(sK1,X0),X0)
      | k2_relat_1(sK1) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f28,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f94,plain,(
    ! [X4] :
      ( sK2(sK1,k1_tarski(X4)) = k1_funct_1(sK1,sK3(sK1,k1_tarski(X4)))
      | k2_relat_1(sK1) = k1_tarski(X4)
      | sK2(sK1,k1_tarski(X4)) = X4 ) ),
    inference(resolution,[],[f54,f49])).

fof(f54,plain,(
    ! [X1] :
      ( r2_hidden(sK2(sK1,X1),X1)
      | sK2(sK1,X1) = k1_funct_1(sK1,sK3(sK1,X1))
      | k2_relat_1(sK1) = X1 ) ),
    inference(subsumption_resolution,[],[f51,f27])).

fof(f51,plain,(
    ! [X1] :
      ( sK2(sK1,X1) = k1_funct_1(sK1,sK3(sK1,X1))
      | r2_hidden(sK2(sK1,X1),X1)
      | k2_relat_1(sK1) = X1
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f28,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1))
      | r2_hidden(sK2(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) != sK2(X0,X1)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (19314)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.49  % (19337)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (19335)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (19320)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (19327)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (19329)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (19318)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (19329)Refutation not found, incomplete strategy% (19329)------------------------------
% 0.21/0.51  % (19329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (19329)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (19329)Memory used [KB]: 10618
% 0.21/0.51  % (19329)Time elapsed: 0.111 s
% 0.21/0.51  % (19329)------------------------------
% 0.21/0.51  % (19329)------------------------------
% 0.21/0.51  % (19315)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (19313)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (19316)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (19317)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (19327)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f244,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.21/0.52    inference(equality_resolution,[],[f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.21/0.52    inference(equality_resolution,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    ~r2_hidden(sK0,k1_tarski(sK0))),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f242])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    sK5(sK1) != sK5(sK1) | ~r2_hidden(sK0,k1_tarski(sK0))),
% 0.21/0.52    inference(superposition,[],[f236,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    k1_funct_1(sK1,sK0) = sK5(sK1)),
% 0.21/0.52    inference(backward_demodulation,[],[f75,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    sK0 = sK4(sK1,sK5(sK1))),
% 0.21/0.52    inference(resolution,[],[f73,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.52    inference(equality_resolution,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    r2_hidden(sK4(sK1,sK5(sK1)),k1_tarski(sK0))),
% 0.21/0.52    inference(forward_demodulation,[],[f72,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    k1_tarski(sK0) = k1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) & k1_tarski(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  fof(f5,conjecture,(
% 0.21/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    r2_hidden(sK4(sK1,sK5(sK1)),k1_relat_1(sK1))),
% 0.21/0.52    inference(subsumption_resolution,[],[f71,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    v1_relat_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    r2_hidden(sK4(sK1,sK5(sK1)),k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f69,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    v1_funct_1(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    r2_hidden(sK4(sK1,sK5(sK1)),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f61,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f19,f18,f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(rectify,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    r2_hidden(sK5(sK1),k2_relat_1(sK1))),
% 0.21/0.52    inference(resolution,[],[f57,f48])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(sK5(sK1),k2_relat_1(sK1))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f55,f27])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | r2_hidden(sK5(sK1),k2_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(superposition,[],[f37,f29])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | r2_hidden(sK5(X1),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(sK5(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(sK5(X1),k2_relat_1(X1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    sK5(sK1) = k1_funct_1(sK1,sK4(sK1,sK5(sK1)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f74,f27])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    sK5(sK1) = k1_funct_1(sK1,sK4(sK1,sK5(sK1))) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f70,f28])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    sK5(sK1) = k1_funct_1(sK1,sK4(sK1,sK5(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f61,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | k1_funct_1(X0,sK4(X0,X5)) = X5 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    ( ! [X0] : (sK5(sK1) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,k1_tarski(sK0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f235,f29])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    ( ! [X0] : (sK5(sK1) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f234,f27])).
% 0.21/0.52  % (19322)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    ( ! [X0] : (sK5(sK1) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f233,f28])).
% 0.21/0.52  fof(f233,plain,(
% 0.21/0.52    ( ! [X0] : (sK5(sK1) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f232,f48])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    ( ! [X0] : (sK5(sK1) != k1_funct_1(sK1,X0) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(sK5(sK1),k1_tarski(sK5(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f231,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    k2_relat_1(sK1) != k1_tarski(sK5(sK1))),
% 0.21/0.52    inference(backward_demodulation,[],[f30,f86])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    ( ! [X0] : (sK5(sK1) != k1_funct_1(sK1,X0) | k2_relat_1(sK1) = k1_tarski(sK5(sK1)) | ~r2_hidden(X0,k1_relat_1(sK1)) | ~r2_hidden(sK5(sK1),k1_tarski(sK5(sK1))) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.21/0.52    inference(superposition,[],[f36,f224])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    sK5(sK1) = sK2(sK1,k1_tarski(sK5(sK1)))),
% 0.21/0.52    inference(subsumption_resolution,[],[f223,f88])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    sK5(sK1) = sK2(sK1,k1_tarski(sK5(sK1))) | k2_relat_1(sK1) = k1_tarski(sK5(sK1))),
% 0.21/0.52    inference(equality_resolution,[],[f202])).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    ( ! [X0] : (sK5(sK1) != X0 | sK2(sK1,k1_tarski(X0)) = X0 | k1_tarski(X0) = k2_relat_1(sK1)) )),
% 0.21/0.52    inference(equality_factoring,[],[f159])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ( ! [X0] : (sK5(sK1) = sK2(sK1,k1_tarski(X0)) | sK2(sK1,k1_tarski(X0)) = X0 | k1_tarski(X0) = k2_relat_1(sK1)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f158,f86])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ( ! [X0] : (k1_funct_1(sK1,sK0) = sK2(sK1,k1_tarski(X0)) | k1_tarski(X0) = k2_relat_1(sK1) | sK2(sK1,k1_tarski(X0)) = X0) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f154])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    ( ! [X0] : (k1_funct_1(sK1,sK0) = sK2(sK1,k1_tarski(X0)) | k1_tarski(X0) = k2_relat_1(sK1) | sK2(sK1,k1_tarski(X0)) = X0 | k1_tarski(X0) = k2_relat_1(sK1) | sK2(sK1,k1_tarski(X0)) = X0) )),
% 0.21/0.53    inference(superposition,[],[f94,f112])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    ( ! [X4] : (sK0 = sK3(sK1,k1_tarski(X4)) | k2_relat_1(sK1) = k1_tarski(X4) | sK2(sK1,k1_tarski(X4)) = X4) )),
% 0.21/0.53    inference(resolution,[],[f77,f49])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(sK2(sK1,X1),X1) | k2_relat_1(sK1) = X1 | sK0 = sK3(sK1,X1)) )),
% 0.21/0.53    inference(resolution,[],[f53,f49])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK3(sK1,X0),k1_tarski(sK0)) | r2_hidden(sK2(sK1,X0),X0) | k2_relat_1(sK1) = X0) )),
% 0.21/0.53    inference(forward_demodulation,[],[f52,f29])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK3(sK1,X0),k1_relat_1(sK1)) | r2_hidden(sK2(sK1,X0),X0) | k2_relat_1(sK1) = X0) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f50,f27])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK3(sK1,X0),k1_relat_1(sK1)) | r2_hidden(sK2(sK1,X0),X0) | k2_relat_1(sK1) = X0 | ~v1_relat_1(sK1)) )),
% 0.21/0.53    inference(resolution,[],[f28,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK3(X0,X1),k1_relat_1(X0)) | r2_hidden(sK2(X0,X1),X1) | k2_relat_1(X0) = X1 | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ( ! [X4] : (sK2(sK1,k1_tarski(X4)) = k1_funct_1(sK1,sK3(sK1,k1_tarski(X4))) | k2_relat_1(sK1) = k1_tarski(X4) | sK2(sK1,k1_tarski(X4)) = X4) )),
% 0.21/0.53    inference(resolution,[],[f54,f49])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(sK2(sK1,X1),X1) | sK2(sK1,X1) = k1_funct_1(sK1,sK3(sK1,X1)) | k2_relat_1(sK1) = X1) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f51,f27])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X1] : (sK2(sK1,X1) = k1_funct_1(sK1,sK3(sK1,X1)) | r2_hidden(sK2(sK1,X1),X1) | k2_relat_1(sK1) = X1 | ~v1_relat_1(sK1)) )),
% 0.21/0.53    inference(resolution,[],[f28,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | sK2(X0,X1) = k1_funct_1(X0,sK3(X0,X1)) | r2_hidden(sK2(X0,X1),X1) | k2_relat_1(X0) = X1 | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) != sK2(X0,X1) | k2_relat_1(X0) = X1 | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK2(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (19327)------------------------------
% 0.21/0.53  % (19327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19327)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (19327)Memory used [KB]: 1791
% 0.21/0.53  % (19327)Time elapsed: 0.067 s
% 0.21/0.53  % (19327)------------------------------
% 0.21/0.53  % (19327)------------------------------
% 0.21/0.53  % (19311)Success in time 0.166 s
%------------------------------------------------------------------------------
