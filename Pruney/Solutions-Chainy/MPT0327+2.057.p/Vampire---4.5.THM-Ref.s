%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:56 EST 2020

% Result     : Theorem 52.70s
% Output     : Refutation 53.15s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 855 expanded)
%              Number of leaves         :   30 ( 232 expanded)
%              Depth                    :   26
%              Number of atoms          :  477 (4148 expanded)
%              Number of equality atoms :  100 ( 557 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f145,f397,f9998,f10086,f10369,f45063,f59573,f60095])).

fof(f60095,plain,
    ( spl6_2
    | ~ spl6_9
    | ~ spl6_74
    | ~ spl6_75 ),
    inference(avatar_contradiction_clause,[],[f60094])).

fof(f60094,plain,
    ( $false
    | spl6_2
    | ~ spl6_9
    | ~ spl6_74
    | ~ spl6_75 ),
    inference(subsumption_resolution,[],[f60093,f144])).

fof(f144,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl6_2
  <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f60093,plain,
    ( sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl6_9
    | ~ spl6_74
    | ~ spl6_75 ),
    inference(forward_demodulation,[],[f60092,f396])).

fof(f396,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl6_9
  <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f60092,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl6_74
    | ~ spl6_75 ),
    inference(forward_demodulation,[],[f60091,f155])).

fof(f155,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f153,f55])).

fof(f55,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f153,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f62,f107])).

fof(f107,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f105,f55])).

fof(f105,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f69,f58])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f60091,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0)
    | ~ spl6_74
    | ~ spl6_75 ),
    inference(forward_demodulation,[],[f60090,f5856])).

fof(f5856,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f5686,f580])).

fof(f580,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X13,X12)) = X12 ),
    inference(resolution,[],[f575,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f575,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(duplicate_literal_removal,[],[f571])).

fof(f571,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X0))
      | r1_xboole_0(X0,k4_xboole_0(X1,X0)) ) ),
    inference(resolution,[],[f126,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f126,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK2(X3,k4_xboole_0(X4,X5)),X5)
      | r1_xboole_0(X3,k4_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f95,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f5686,plain,(
    ! [X101,X102] : k1_xboole_0 = k3_xboole_0(X101,k4_xboole_0(X102,X101)) ),
    inference(resolution,[],[f5638,f279])).

fof(f279,plain,(
    ! [X21] :
      ( r2_hidden(sK3(X21,k1_xboole_0),X21)
      | k1_xboole_0 = X21 ) ),
    inference(resolution,[],[f70,f129])).

fof(f129,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(condensation,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f95,f107])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f5638,plain,(
    ! [X10,X11,X9] : ~ r2_hidden(X9,k3_xboole_0(X10,k4_xboole_0(X11,X10))) ),
    inference(subsumption_resolution,[],[f5622,f4387])).

fof(f4387,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f4385,f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f4385,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f4368])).

fof(f4368,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f1111,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1111,plain,(
    ! [X6,X7,X5] :
      ( r2_hidden(sK4(k3_xboole_0(X5,X6),X7),X5)
      | r1_tarski(k3_xboole_0(X5,X6),X7) ) ),
    inference(subsumption_resolution,[],[f1097,f96])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1097,plain,(
    ! [X6,X7,X5] :
      ( r2_hidden(sK4(k3_xboole_0(X5,X6),X7),k4_xboole_0(X5,X6))
      | r2_hidden(sK4(k3_xboole_0(X5,X6),X7),X5)
      | r1_tarski(k3_xboole_0(X5,X6),X7) ) ),
    inference(superposition,[],[f253,f61])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f253,plain,(
    ! [X10,X11,X9] :
      ( r2_hidden(sK4(X9,X10),k5_xboole_0(X11,X9))
      | r2_hidden(sK4(X9,X10),X11)
      | r1_tarski(X9,X10) ) ),
    inference(resolution,[],[f92,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f5622,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X9,X10)
      | ~ r2_hidden(X9,k3_xboole_0(X10,k4_xboole_0(X11,X10))) ) ),
    inference(resolution,[],[f5520,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5520,plain,(
    ! [X4,X5] : r1_xboole_0(k3_xboole_0(X4,k4_xboole_0(X5,X4)),X4) ),
    inference(resolution,[],[f5338,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f5338,plain,(
    ! [X134,X135] : r1_xboole_0(k3_xboole_0(X134,k4_xboole_0(X135,X134)),k2_xboole_0(X134,X135)) ),
    inference(subsumption_resolution,[],[f5311,f67])).

fof(f5311,plain,(
    ! [X134,X135] :
      ( ~ r2_hidden(sK2(k3_xboole_0(X134,k4_xboole_0(X135,X134)),k2_xboole_0(X134,X135)),k2_xboole_0(X134,X135))
      | r1_xboole_0(k3_xboole_0(X134,k4_xboole_0(X135,X134)),k2_xboole_0(X134,X135)) ) ),
    inference(superposition,[],[f841,f5212])).

fof(f5212,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(k2_xboole_0(X2,X3),k3_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(backward_demodulation,[],[f206,f2056])).

fof(f2056,plain,(
    ! [X8,X7] : k2_xboole_0(X8,X7) = k2_xboole_0(X8,k4_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f2007,f62])).

fof(f2007,plain,(
    ! [X8,X7] : k2_xboole_0(X8,k4_xboole_0(X7,X8)) = k5_xboole_0(X8,k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f62,f562])).

fof(f562,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k4_xboole_0(k4_xboole_0(X12,X13),X13) ),
    inference(resolution,[],[f557,f75])).

fof(f557,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f553])).

fof(f553,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k4_xboole_0(X0,X1),X1)
      | r1_xboole_0(k4_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f125,f67])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X1)
      | r1_xboole_0(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f95,f66])).

fof(f206,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k5_xboole_0(k2_xboole_0(X2,X3),k3_xboole_0(X2,k4_xboole_0(X3,X2))) ),
    inference(superposition,[],[f65,f62])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f841,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),k5_xboole_0(X1,X0))
      | r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f832])).

fof(f832,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),k5_xboole_0(X1,X0))
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f241,f66])).

fof(f241,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(sK2(X6,X7),X8)
      | ~ r2_hidden(sK2(X6,X7),k5_xboole_0(X7,X8))
      | r1_xboole_0(X6,X7) ) ),
    inference(resolution,[],[f90,f67])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f60090,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k3_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)))
    | ~ spl6_74
    | ~ spl6_75 ),
    inference(forward_demodulation,[],[f59779,f45062])).

fof(f45062,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f45060])).

fof(f45060,plain,
    ( spl6_74
  <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f59779,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),sK1)) = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k3_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),sK1)))
    | ~ spl6_75 ),
    inference(superposition,[],[f209,f58236])).

fof(f58236,plain,
    ( k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl6_75 ),
    inference(avatar_component_clause,[],[f58234])).

fof(f58234,plain,
    ( spl6_75
  <=> k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f209,plain,(
    ! [X6,X7] : k2_xboole_0(k5_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k5_xboole_0(k2_xboole_0(X6,X7),k3_xboole_0(k5_xboole_0(X6,X7),k3_xboole_0(X6,X7))) ),
    inference(superposition,[],[f65,f65])).

fof(f59573,plain,
    ( spl6_75
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f38625,f10261,f58234])).

fof(f10261,plain,
    ( spl6_53
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f38625,plain,
    ( k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl6_53 ),
    inference(forward_demodulation,[],[f38624,f147])).

fof(f147,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f132,f69])).

fof(f132,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(resolution,[],[f129,f73])).

fof(f38624,plain,
    ( k5_xboole_0(k1_tarski(sK0),sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl6_53 ),
    inference(forward_demodulation,[],[f38504,f146])).

fof(f146,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f131,f75])).

fof(f131,plain,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f129,f67])).

fof(f38504,plain,
    ( k5_xboole_0(k1_tarski(sK0),sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_xboole_0))
    | ~ spl6_53 ),
    inference(superposition,[],[f38480,f10263])).

fof(f10263,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f10261])).

fof(f38480,plain,(
    ! [X4,X5] : k5_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f38479,f155])).

fof(f38479,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,X5))) = k5_xboole_0(k5_xboole_0(X4,X5),k1_xboole_0) ),
    inference(forward_demodulation,[],[f748,f5686])).

fof(f748,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,X5))) = k5_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,X5)))) ),
    inference(superposition,[],[f206,f64])).

fof(f64,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f45063,plain,
    ( spl6_74
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f44596,f394,f45060])).

fof(f44596,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl6_9 ),
    inference(superposition,[],[f44287,f396])).

fof(f44287,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k2_xboole_0(X3,X4)) = X3 ),
    inference(superposition,[],[f11628,f55])).

fof(f11628,plain,(
    ! [X54,X55] : k2_xboole_0(k3_xboole_0(X54,k2_xboole_0(X54,X55)),k1_xboole_0) = X54 ),
    inference(superposition,[],[f63,f11272])).

fof(f11272,plain,(
    ! [X196,X197] : k1_xboole_0 = k4_xboole_0(X196,k2_xboole_0(X196,X197)) ),
    inference(resolution,[],[f9968,f279])).

fof(f9968,plain,(
    ! [X10,X11,X9] : ~ r2_hidden(X9,k4_xboole_0(X10,k2_xboole_0(X10,X11))) ),
    inference(subsumption_resolution,[],[f9952,f96])).

fof(f9952,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X9,k4_xboole_0(X10,k2_xboole_0(X10,X11)))
      | ~ r2_hidden(X9,X10) ) ),
    inference(resolution,[],[f9888,f68])).

fof(f9888,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f8208,f62])).

fof(f8208,plain,(
    ! [X6,X4,X5] : r1_xboole_0(X6,k4_xboole_0(X4,k5_xboole_0(X6,k4_xboole_0(X5,X4)))) ),
    inference(superposition,[],[f7843,f580])).

fof(f7843,plain,(
    ! [X8,X7,X9] : r1_xboole_0(X7,k4_xboole_0(k4_xboole_0(X8,X9),k5_xboole_0(X7,X9))) ),
    inference(duplicate_literal_removal,[],[f7808])).

fof(f7808,plain,(
    ! [X8,X7,X9] :
      ( r1_xboole_0(X7,k4_xboole_0(k4_xboole_0(X8,X9),k5_xboole_0(X7,X9)))
      | r1_xboole_0(X7,k4_xboole_0(k4_xboole_0(X8,X9),k5_xboole_0(X7,X9))) ) ),
    inference(resolution,[],[f912,f625])).

fof(f625,plain,(
    ! [X30,X28,X31,X29] :
      ( ~ r2_hidden(sK2(X28,k4_xboole_0(k4_xboole_0(X29,X30),X31)),X30)
      | r1_xboole_0(X28,k4_xboole_0(k4_xboole_0(X29,X30),X31)) ) ),
    inference(resolution,[],[f134,f95])).

fof(f134,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK2(X3,k4_xboole_0(X4,X5)),X4)
      | r1_xboole_0(X3,k4_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f96,f67])).

fof(f912,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,k4_xboole_0(X1,k5_xboole_0(X0,X2))),X2)
      | r1_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,X2))) ) ),
    inference(duplicate_literal_removal,[],[f890])).

fof(f890,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,k4_xboole_0(X1,k5_xboole_0(X0,X2))),X2)
      | r1_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,X2)))
      | r1_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,X2))) ) ),
    inference(resolution,[],[f245,f126])).

fof(f245,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK2(X3,X4),k5_xboole_0(X3,X5))
      | r2_hidden(sK2(X3,X4),X5)
      | r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f91,f66])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f10369,plain,
    ( spl6_53
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f10220,f10084,f10261])).

fof(f10084,plain,
    ( spl6_50
  <=> ! [X3] : ~ r2_hidden(X3,k4_xboole_0(k1_tarski(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f10220,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl6_50 ),
    inference(resolution,[],[f10085,f2152])).

fof(f2152,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK5(k1_xboole_0,X4,X5),X5)
      | k1_xboole_0 = X5 ) ),
    inference(forward_demodulation,[],[f2151,f507])).

fof(f507,plain,(
    ! [X26] : k1_xboole_0 = k4_xboole_0(X26,X26) ),
    inference(resolution,[],[f325,f129])).

fof(f325,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X0,X1),X1)
      | k4_xboole_0(X0,X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f322])).

fof(f322,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X0) = X1
      | r2_hidden(sK5(X0,X0,X1),X1)
      | r2_hidden(sK5(X0,X0,X1),X1)
      | k4_xboole_0(X0,X0) = X1 ) ),
    inference(resolution,[],[f87,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2151,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = X5
      | r2_hidden(sK5(k4_xboole_0(X3,X3),X4,X5),X5) ) ),
    inference(forward_demodulation,[],[f2150,f107])).

fof(f2150,plain,(
    ! [X4,X5,X3] :
      ( k4_xboole_0(k1_xboole_0,X4) = X5
      | r2_hidden(sK5(k4_xboole_0(X3,X3),X4,X5),X5) ) ),
    inference(forward_demodulation,[],[f2148,f507])).

fof(f2148,plain,(
    ! [X4,X5,X3] :
      ( k4_xboole_0(k4_xboole_0(X3,X3),X4) = X5
      | r2_hidden(sK5(k4_xboole_0(X3,X3),X4,X5),X5) ) ),
    inference(duplicate_literal_removal,[],[f2138])).

fof(f2138,plain,(
    ! [X4,X5,X3] :
      ( k4_xboole_0(k4_xboole_0(X3,X3),X4) = X5
      | r2_hidden(sK5(k4_xboole_0(X3,X3),X4,X5),X5)
      | r2_hidden(sK5(k4_xboole_0(X3,X3),X4,X5),X5)
      | k4_xboole_0(k4_xboole_0(X3,X3),X4) = X5 ) ),
    inference(resolution,[],[f306,f305])).

fof(f305,plain,(
    ! [X19,X17,X18,X16] :
      ( r2_hidden(sK5(k4_xboole_0(X16,X17),X18,X19),X19)
      | r2_hidden(sK5(k4_xboole_0(X16,X17),X18,X19),X16)
      | k4_xboole_0(k4_xboole_0(X16,X17),X18) = X19 ) ),
    inference(resolution,[],[f86,f96])).

fof(f306,plain,(
    ! [X23,X21,X22,X20] :
      ( ~ r2_hidden(sK5(k4_xboole_0(X20,X21),X22,X23),X21)
      | k4_xboole_0(k4_xboole_0(X20,X21),X22) = X23
      | r2_hidden(sK5(k4_xboole_0(X20,X21),X22,X23),X23) ) ),
    inference(resolution,[],[f86,f95])).

fof(f10085,plain,
    ( ! [X3] : ~ r2_hidden(X3,k4_xboole_0(k1_tarski(sK0),sK1))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f10084])).

fof(f10086,plain,
    ( spl6_50
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f10029,f9995,f10084])).

fof(f9995,plain,
    ( spl6_49
  <=> r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f10029,plain,
    ( ! [X3] : ~ r2_hidden(X3,k4_xboole_0(k1_tarski(sK0),sK1))
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f10027,f96])).

fof(f10027,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k4_xboole_0(k1_tarski(sK0),sK1))
        | ~ r2_hidden(X3,k1_tarski(sK0)) )
    | ~ spl6_49 ),
    inference(resolution,[],[f9997,f68])).

fof(f9997,plain,
    ( r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),sK1))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f9995])).

fof(f9998,plain,
    ( spl6_49
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f9964,f394,f9995])).

fof(f9964,plain,
    ( r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),sK1))
    | ~ spl6_9 ),
    inference(superposition,[],[f9888,f396])).

fof(f397,plain,
    ( spl6_9
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f382,f98,f394])).

fof(f98,plain,
    ( spl6_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f382,plain,
    ( sK1 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl6_1 ),
    inference(resolution,[],[f106,f100])).

fof(f100,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f106,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | k2_xboole_0(k1_tarski(X2),X3) = X3 ) ),
    inference(resolution,[],[f69,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f145,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f54,f142])).

fof(f54,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f101,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f53,f98])).

fof(f53,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:51:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (17287)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
% 1.43/0.55  % (17304)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.43/0.55  % (17296)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.43/0.56  % (17288)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
% 1.43/0.57  % (17303)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_157 on theBenchmark
% 1.43/0.57  % (17295)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
% 1.60/0.58  % (17294)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% 1.60/0.58  % (17295)Refutation not found, incomplete strategy% (17295)------------------------------
% 1.60/0.58  % (17295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (17282)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.60/0.58  % (17295)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (17295)Memory used [KB]: 6268
% 1.60/0.58  % (17295)Time elapsed: 0.150 s
% 1.60/0.58  % (17295)------------------------------
% 1.60/0.58  % (17295)------------------------------
% 1.60/0.59  % (17285)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 1.60/0.59  % (17284)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 1.60/0.60  % (17286)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
% 1.60/0.60  % (17281)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
% 1.60/0.60  % (17290)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% 1.60/0.61  % (17297)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_23 on theBenchmark
% 1.60/0.61  % (17308)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% 1.60/0.61  % (17301)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
% 1.60/0.61  % (17310)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_48 on theBenchmark
% 1.60/0.61  % (17289)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% 1.60/0.61  % (17292)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% 1.60/0.61  % (17293)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 1.60/0.62  % (17306)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_88 on theBenchmark
% 1.60/0.62  % (17305)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.60/0.62  % (17302)ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=input_only:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70 on theBenchmark
% 1.60/0.62  % (17305)Refutation not found, incomplete strategy% (17305)------------------------------
% 1.60/0.62  % (17305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.62  % (17305)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.62  
% 1.60/0.62  % (17305)Memory used [KB]: 10618
% 1.60/0.62  % (17305)Time elapsed: 0.188 s
% 1.60/0.62  % (17305)------------------------------
% 1.60/0.62  % (17305)------------------------------
% 1.60/0.62  % (17283)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
% 1.60/0.62  % (17300)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 1.60/0.62  % (17309)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4 on theBenchmark
% 1.60/0.63  % (17299)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_11 on theBenchmark
% 1.60/0.64  % (17291)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_3 on theBenchmark
% 2.19/0.65  % (17298)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% 2.19/0.67  % (17307)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
% 2.73/0.74  % (17288)Refutation not found, incomplete strategy% (17288)------------------------------
% 2.73/0.74  % (17288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.73/0.74  % (17288)Termination reason: Refutation not found, incomplete strategy
% 2.89/0.75  
% 2.89/0.75  % (17288)Memory used [KB]: 6140
% 2.89/0.75  % (17288)Time elapsed: 0.256 s
% 2.89/0.75  % (17288)------------------------------
% 2.89/0.75  % (17288)------------------------------
% 2.89/0.76  % (17347)dis+1011_8:1_aac=none:acc=on:afp=1000:afq=1.4:amm=off:anc=all:bs=unit_only:bce=on:ccuc=small_ones:fsr=off:fde=unused:gsp=input_only:gs=on:gsem=off:lma=on:nm=16:nwc=2.5:sd=4:ss=axioms:st=1.5:sos=all:uhcvi=on_65 on theBenchmark
% 2.89/0.81  % (17348)ott+1_5:1_acc=on:add=off:afr=on:afp=100000:afq=1.1:amm=sco:anc=none:lcm=predicate:nm=16:nwc=1.1:sd=1:ss=axioms:st=3.0:sos=on:sac=on:updr=off_18 on theBenchmark
% 3.39/0.86  % (17352)lrs+1002_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:cond=fast:fde=none:gs=on:gsem=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence_8 on theBenchmark
% 3.39/0.86  % (17352)Refutation not found, incomplete strategy% (17352)------------------------------
% 3.39/0.86  % (17352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.39/0.86  % (17352)Termination reason: Refutation not found, incomplete strategy
% 3.39/0.86  
% 3.39/0.86  % (17352)Memory used [KB]: 10618
% 3.39/0.86  % (17352)Time elapsed: 0.054 s
% 3.39/0.86  % (17352)------------------------------
% 3.39/0.86  % (17352)------------------------------
% 4.57/0.99  % (17399)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_4 on theBenchmark
% 5.41/1.06  % (17291)Time limit reached!
% 5.41/1.06  % (17291)------------------------------
% 5.41/1.06  % (17291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.41/1.06  % (17291)Termination reason: Time limit
% 5.41/1.06  
% 5.41/1.06  % (17291)Memory used [KB]: 13560
% 5.41/1.06  % (17291)Time elapsed: 0.630 s
% 5.41/1.06  % (17291)------------------------------
% 5.41/1.06  % (17291)------------------------------
% 6.02/1.18  % (17500)lrs+1002_3:1_av=off:bd=off:cond=fast:fde=none:gsp=input_only:lcm=predicate:lma=on:lwlo=on:nm=4:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_134 on theBenchmark
% 6.90/1.25  % (17307)Time limit reached!
% 6.90/1.25  % (17307)------------------------------
% 6.90/1.25  % (17307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.90/1.25  % (17307)Termination reason: Time limit
% 6.90/1.25  % (17307)Termination phase: Saturation
% 6.90/1.25  
% 6.90/1.25  % (17307)Memory used [KB]: 14967
% 6.90/1.25  % (17307)Time elapsed: 0.800 s
% 6.90/1.25  % (17307)------------------------------
% 6.90/1.25  % (17307)------------------------------
% 7.61/1.37  % (17541)dis+10_5_av=off:bce=on:cond=on:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=6:nwc=1:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_6 on theBenchmark
% 7.61/1.37  % (17541)Refutation not found, incomplete strategy% (17541)------------------------------
% 7.61/1.37  % (17541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.61/1.37  % (17541)Termination reason: Refutation not found, incomplete strategy
% 7.61/1.37  
% 7.61/1.37  % (17541)Memory used [KB]: 6268
% 7.61/1.37  % (17541)Time elapsed: 0.061 s
% 7.61/1.37  % (17541)------------------------------
% 7.61/1.37  % (17541)------------------------------
% 8.25/1.44  % (17300)Time limit reached!
% 8.25/1.44  % (17300)------------------------------
% 8.25/1.44  % (17300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.25/1.44  % (17300)Termination reason: Time limit
% 8.25/1.44  
% 8.25/1.44  % (17300)Memory used [KB]: 4733
% 8.25/1.44  % (17300)Time elapsed: 1.008 s
% 8.25/1.44  % (17300)------------------------------
% 8.25/1.44  % (17300)------------------------------
% 8.25/1.47  % (17290)Time limit reached!
% 8.25/1.47  % (17290)------------------------------
% 8.25/1.47  % (17290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.25/1.47  % (17290)Termination reason: Time limit
% 8.25/1.47  
% 8.25/1.47  % (17290)Memory used [KB]: 16375
% 8.25/1.47  % (17290)Time elapsed: 1.025 s
% 8.25/1.47  % (17290)------------------------------
% 8.25/1.47  % (17290)------------------------------
% 8.65/1.49  % (17583)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_243 on theBenchmark
% 9.25/1.58  % (17584)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_254 on theBenchmark
% 9.25/1.61  % (17296)Time limit reached!
% 9.25/1.61  % (17296)------------------------------
% 9.25/1.61  % (17296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.25/1.61  % (17296)Termination reason: Time limit
% 9.25/1.61  
% 9.25/1.61  % (17296)Memory used [KB]: 13432
% 9.25/1.61  % (17296)Time elapsed: 1.114 s
% 9.25/1.61  % (17296)------------------------------
% 9.25/1.61  % (17296)------------------------------
% 9.96/1.63  % (17309)Time limit reached!
% 9.96/1.63  % (17309)------------------------------
% 9.96/1.63  % (17309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.96/1.63  % (17309)Termination reason: Time limit
% 9.96/1.63  % (17309)Termination phase: Saturation
% 9.96/1.63  
% 9.96/1.63  % (17309)Memory used [KB]: 13688
% 9.96/1.63  % (17309)Time elapsed: 0.800 s
% 9.96/1.63  % (17309)------------------------------
% 9.96/1.63  % (17309)------------------------------
% 9.96/1.63  % (17585)ins+10_1_av=off:fde=none:gsp=input_only:irw=on:igbrr=0.7:igpr=on:igrr=16/1:igrp=400:igrpq=2.0:igs=1003:igwr=on:lcm=predicate:lma=on:nm=64:newcnf=on:nwc=3:sp=occurrence:uhcvi=on_62 on theBenchmark
% 9.96/1.64  % (17286)Time limit reached!
% 9.96/1.64  % (17286)------------------------------
% 9.96/1.64  % (17286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.96/1.64  % (17286)Termination reason: Time limit
% 9.96/1.64  
% 9.96/1.64  % (17286)Memory used [KB]: 8827
% 9.96/1.64  % (17286)Time elapsed: 1.211 s
% 9.96/1.64  % (17286)------------------------------
% 9.96/1.64  % (17286)------------------------------
% 9.96/1.65  % (17284)Time limit reached!
% 9.96/1.65  % (17284)------------------------------
% 9.96/1.65  % (17284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.25/1.67  % (17284)Termination reason: Time limit
% 10.25/1.67  % (17284)Termination phase: Saturation
% 10.25/1.67  
% 10.25/1.67  % (17284)Memory used [KB]: 12281
% 10.25/1.67  % (17284)Time elapsed: 1.200 s
% 10.25/1.67  % (17284)------------------------------
% 10.25/1.67  % (17284)------------------------------
% 10.84/1.74  % (17586)ins+11_64_av=off:cond=fast:fde=none:gs=on:gsem=on:igbrr=0.7:igrr=1/2:igrp=4000:igrpq=1.2:igwr=on:lcm=predicate:lma=on:nwc=1.1:sd=2:ss=axioms:st=3.0:sos=on:sp=occurrence_38 on theBenchmark
% 10.84/1.75  % (17588)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_27 on theBenchmark
% 10.84/1.76  % (17399)Time limit reached!
% 10.84/1.76  % (17399)------------------------------
% 10.84/1.76  % (17399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.84/1.76  % (17399)Termination reason: Time limit
% 10.84/1.76  
% 10.84/1.76  % (17399)Memory used [KB]: 15863
% 10.84/1.76  % (17399)Time elapsed: 0.828 s
% 10.84/1.76  % (17399)------------------------------
% 10.84/1.76  % (17399)------------------------------
% 10.84/1.77  % (17587)lrs+10_2:3_afp=1000:afq=1.1:amm=sco:anc=none:er=known:lcm=reverse:lwlo=on:nm=64:newcnf=on:nwc=2:stl=30:sd=5:ss=axioms:sos=theory:sac=on:sp=occurrence_78 on theBenchmark
% 11.09/1.78  % (17304)Time limit reached!
% 11.09/1.78  % (17304)------------------------------
% 11.09/1.78  % (17304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.09/1.79  % (17304)Termination reason: Time limit
% 11.09/1.79  % (17304)Termination phase: Saturation
% 11.09/1.79  
% 11.09/1.79  % (17304)Memory used [KB]: 17526
% 11.09/1.79  % (17304)Time elapsed: 1.300 s
% 11.09/1.79  % (17304)------------------------------
% 11.09/1.79  % (17304)------------------------------
% 11.09/1.80  % (17589)lrs-2_3:1_add=off:afr=on:afp=1000:afq=1.2:amm=sco:anc=all_dependent:bd=off:bs=unit_only:bsr=on:cond=on:fde=unused:gs=on:gsem=on:irw=on:lcm=reverse:nm=32:nwc=1.7:sas=z3:stl=30:sos=all:sac=on_28 on theBenchmark
% 11.63/1.89  % (17591)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_4 on theBenchmark
% 11.63/1.91  % (17590)lrs+1002_2:1_acc=on:add=large:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:ccuc=first:fsr=off:gs=on:irw=on:nm=32:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:sos=on:sp=reverse_arity_3 on theBenchmark
% 11.63/1.91  % (17590)Refutation not found, incomplete strategy% (17590)------------------------------
% 11.63/1.91  % (17590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.63/1.91  % (17590)Termination reason: Refutation not found, incomplete strategy
% 11.63/1.91  
% 11.63/1.91  % (17590)Memory used [KB]: 10618
% 11.63/1.91  % (17590)Time elapsed: 0.130 s
% 11.63/1.91  % (17590)------------------------------
% 11.63/1.91  % (17590)------------------------------
% 12.32/2.03  % (17289)Time limit reached!
% 12.32/2.03  % (17289)------------------------------
% 12.32/2.03  % (17289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.32/2.03  % (17289)Termination reason: Time limit
% 12.32/2.03  % (17289)Termination phase: Saturation
% 12.32/2.03  
% 12.32/2.03  % (17289)Memory used [KB]: 19317
% 12.32/2.03  % (17289)Time elapsed: 1.600 s
% 12.32/2.03  % (17289)------------------------------
% 12.32/2.03  % (17289)------------------------------
% 12.88/2.04  % (17592)ott-11_3_av=off:bsr=on:cond=fast:fde=unused:lcm=predicate:lma=on:nm=6:nwc=1:sos=on:updr=off_546 on theBenchmark
% 12.88/2.04  % (17299)Time limit reached!
% 12.88/2.04  % (17299)------------------------------
% 12.88/2.04  % (17299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.88/2.04  % (17299)Termination reason: Time limit
% 12.88/2.04  % (17299)Termination phase: Saturation
% 12.88/2.04  
% 12.88/2.04  % (17299)Memory used [KB]: 20468
% 12.88/2.04  % (17299)Time elapsed: 1.600 s
% 12.88/2.04  % (17299)------------------------------
% 12.88/2.04  % (17299)------------------------------
% 12.88/2.04  % (17592)Refutation not found, incomplete strategy% (17592)------------------------------
% 12.88/2.04  % (17592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.88/2.04  % (17592)Termination reason: Refutation not found, incomplete strategy
% 12.88/2.04  
% 12.88/2.04  % (17592)Memory used [KB]: 1663
% 12.88/2.04  % (17592)Time elapsed: 0.096 s
% 12.88/2.04  % (17592)------------------------------
% 12.88/2.04  % (17592)------------------------------
% 12.88/2.06  % (17281)Time limit reached!
% 12.88/2.06  % (17281)------------------------------
% 12.88/2.06  % (17281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.88/2.06  % (17281)Termination reason: Time limit
% 12.88/2.06  
% 12.88/2.06  % (17281)Memory used [KB]: 17398
% 12.88/2.06  % (17281)Time elapsed: 1.614 s
% 12.88/2.06  % (17281)------------------------------
% 12.88/2.06  % (17281)------------------------------
% 14.25/2.17  % (17593)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_138 on theBenchmark
% 14.25/2.18  % (17595)ott+1004_12_awrs=converge:awrsf=64:aac=none:afr=on:afp=4000:afq=1.4:amm=sco:anc=none:bs=on:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=on:lma=on:nwc=5:nicw=on:sas=z3:sos=all:sac=on:sp=occurrence:urr=ec_only_113 on theBenchmark
% 14.25/2.18  % (17594)lrs+11_8:1_av=off:bd=preordered:br=off:cond=on:gs=on:gsem=on:lcm=reverse:lma=on:nm=0:nwc=1:stl=60:urr=on_362 on theBenchmark
% 14.25/2.20  % (17596)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_41 on theBenchmark
% 17.44/2.57  % (17293)Time limit reached!
% 17.44/2.57  % (17293)------------------------------
% 17.44/2.57  % (17293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.44/2.57  % (17293)Termination reason: Time limit
% 17.44/2.57  
% 17.44/2.57  % (17293)Memory used [KB]: 11129
% 17.44/2.57  % (17293)Time elapsed: 2.124 s
% 17.44/2.57  % (17293)------------------------------
% 17.44/2.57  % (17293)------------------------------
% 17.44/2.63  % (17591)Time limit reached!
% 17.44/2.63  % (17591)------------------------------
% 17.44/2.63  % (17591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.44/2.64  % (17591)Termination reason: Time limit
% 17.44/2.64  % (17591)Termination phase: Saturation
% 17.44/2.64  
% 17.44/2.64  % (17591)Memory used [KB]: 19829
% 17.44/2.64  % (17591)Time elapsed: 0.809 s
% 17.44/2.64  % (17591)------------------------------
% 17.44/2.64  % (17591)------------------------------
% 18.29/2.70  % (17597)dis+1010_128_afr=on:afp=10000:afq=1.1:anc=none:bsr=on:br=off:bce=on:cond=on:fsr=off:gsp=input_only:irw=on:nm=6:newcnf=on:nwc=1.5:sos=all:sac=on:sp=occurrence:urr=on:updr=off_107 on theBenchmark
% 18.80/2.75  % (17598)lrs+1002_8:1_add=large:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:bd=off:bsr=on:er=known:lwlo=on:nm=0:nwc=1.2:stl=30:sd=1:ss=axioms:sp=occurrence:updr=off_51 on theBenchmark
% 19.85/2.87  % (17287)Time limit reached!
% 19.85/2.87  % (17287)------------------------------
% 19.85/2.87  % (17287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.85/2.88  % (17287)Termination reason: Time limit
% 19.85/2.88  
% 19.85/2.88  % (17287)Memory used [KB]: 50788
% 19.85/2.88  % (17287)Time elapsed: 2.439 s
% 19.85/2.88  % (17287)------------------------------
% 19.85/2.88  % (17287)------------------------------
% 22.20/3.21  % (17348)Time limit reached!
% 22.20/3.21  % (17348)------------------------------
% 22.20/3.21  % (17348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 22.20/3.21  % (17348)Termination reason: Time limit
% 22.20/3.21  
% 22.20/3.21  % (17348)Memory used [KB]: 15863
% 22.20/3.21  % (17348)Time elapsed: 2.521 s
% 22.20/3.21  % (17348)------------------------------
% 22.20/3.21  % (17348)------------------------------
% 23.88/3.41  % (17282)Time limit reached!
% 23.88/3.41  % (17282)------------------------------
% 23.88/3.41  % (17282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.88/3.41  % (17282)Termination reason: Time limit
% 23.88/3.41  
% 23.88/3.41  % (17282)Memory used [KB]: 38250
% 23.88/3.41  % (17282)Time elapsed: 2.959 s
% 23.88/3.41  % (17282)------------------------------
% 23.88/3.41  % (17282)------------------------------
% 25.99/3.65  % (17297)Time limit reached!
% 25.99/3.65  % (17297)------------------------------
% 25.99/3.65  % (17297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.99/3.65  % (17297)Termination reason: Time limit
% 25.99/3.65  % (17297)Termination phase: Saturation
% 25.99/3.65  
% 25.99/3.65  % (17297)Memory used [KB]: 19957
% 25.99/3.65  % (17297)Time elapsed: 3.100 s
% 25.99/3.65  % (17297)------------------------------
% 25.99/3.65  % (17297)------------------------------
% 35.63/4.85  % (17285)Time limit reached!
% 35.63/4.85  % (17285)------------------------------
% 35.63/4.85  % (17285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 35.63/4.85  % (17285)Termination reason: Time limit
% 35.63/4.85  
% 35.63/4.85  % (17285)Memory used [KB]: 23666
% 35.63/4.85  % (17285)Time elapsed: 4.414 s
% 35.63/4.85  % (17285)------------------------------
% 35.63/4.85  % (17285)------------------------------
% 36.53/5.04  % (17292)Time limit reached!
% 36.53/5.04  % (17292)------------------------------
% 36.53/5.04  % (17292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 37.16/5.04  % (17292)Termination reason: Time limit
% 37.16/5.04  
% 37.16/5.04  % (17292)Memory used [KB]: 26993
% 37.16/5.04  % (17292)Time elapsed: 4.605 s
% 37.16/5.04  % (17292)------------------------------
% 37.16/5.04  % (17292)------------------------------
% 39.58/5.37  % (17588)Time limit reached!
% 39.58/5.37  % (17588)------------------------------
% 39.58/5.37  % (17588)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 39.58/5.37  % (17588)Termination reason: Time limit
% 39.58/5.37  
% 39.58/5.37  % (17588)Memory used [KB]: 21620
% 39.58/5.37  % (17588)Time elapsed: 3.712 s
% 39.58/5.37  % (17588)------------------------------
% 39.58/5.37  % (17588)------------------------------
% 40.57/5.50  % (17589)Time limit reached!
% 40.57/5.50  % (17589)------------------------------
% 40.57/5.50  % (17589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 40.57/5.52  % (17589)Termination reason: Time limit
% 40.57/5.52  % (17589)Termination phase: Saturation
% 40.57/5.52  
% 40.57/5.52  % (17589)Memory used [KB]: 13048
% 40.57/5.52  % (17589)Time elapsed: 3.800 s
% 40.57/5.52  % (17589)------------------------------
% 40.57/5.52  % (17589)------------------------------
% 45.16/6.05  % (17283)Time limit reached!
% 45.16/6.05  % (17283)------------------------------
% 45.16/6.05  % (17283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 45.16/6.05  % (17283)Termination reason: Time limit
% 45.16/6.05  
% 45.16/6.05  % (17283)Memory used [KB]: 45415
% 45.16/6.05  % (17283)Time elapsed: 5.567 s
% 45.16/6.05  % (17283)------------------------------
% 45.16/6.05  % (17283)------------------------------
% 51.43/6.85  % (17310)Time limit reached!
% 51.43/6.85  % (17310)------------------------------
% 51.43/6.85  % (17310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 51.43/6.86  % (17310)Termination reason: Time limit
% 51.43/6.86  % (17310)Termination phase: Saturation
% 51.43/6.86  
% 51.43/6.86  % (17310)Memory used [KB]: 26993
% 51.43/6.86  % (17310)Time elapsed: 6.422 s
% 51.43/6.86  % (17310)------------------------------
% 51.43/6.86  % (17310)------------------------------
% 51.74/6.93  % (17301)Time limit reached!
% 51.74/6.93  % (17301)------------------------------
% 51.74/6.93  % (17301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 51.74/6.93  % (17301)Termination reason: Time limit
% 51.74/6.93  % (17301)Termination phase: Saturation
% 51.74/6.93  
% 51.74/6.93  % (17301)Memory used [KB]: 21108
% 51.74/6.93  % (17301)Time elapsed: 6.500 s
% 51.74/6.93  % (17301)------------------------------
% 51.74/6.93  % (17301)------------------------------
% 51.74/6.93  % (17308)Time limit reached!
% 51.74/6.93  % (17308)------------------------------
% 51.74/6.93  % (17308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 51.74/6.93  % (17308)Termination reason: Time limit
% 51.74/6.93  % (17308)Termination phase: Saturation
% 51.74/6.93  
% 51.74/6.93  % (17308)Memory used [KB]: 43368
% 51.74/6.93  % (17308)Time elapsed: 6.500 s
% 51.74/6.93  % (17308)------------------------------
% 51.74/6.93  % (17308)------------------------------
% 52.70/7.02  % (17593)Refutation found. Thanks to Tanya!
% 52.70/7.02  % SZS status Theorem for theBenchmark
% 53.15/7.04  % SZS output start Proof for theBenchmark
% 53.15/7.04  fof(f60196,plain,(
% 53.15/7.04    $false),
% 53.15/7.04    inference(avatar_sat_refutation,[],[f101,f145,f397,f9998,f10086,f10369,f45063,f59573,f60095])).
% 53.15/7.04  fof(f60095,plain,(
% 53.15/7.04    spl6_2 | ~spl6_9 | ~spl6_74 | ~spl6_75),
% 53.15/7.04    inference(avatar_contradiction_clause,[],[f60094])).
% 53.15/7.04  fof(f60094,plain,(
% 53.15/7.04    $false | (spl6_2 | ~spl6_9 | ~spl6_74 | ~spl6_75)),
% 53.15/7.04    inference(subsumption_resolution,[],[f60093,f144])).
% 53.15/7.04  fof(f144,plain,(
% 53.15/7.04    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | spl6_2),
% 53.15/7.04    inference(avatar_component_clause,[],[f142])).
% 53.15/7.04  fof(f142,plain,(
% 53.15/7.04    spl6_2 <=> sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 53.15/7.04    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 53.15/7.04  fof(f60093,plain,(
% 53.15/7.04    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | (~spl6_9 | ~spl6_74 | ~spl6_75)),
% 53.15/7.04    inference(forward_demodulation,[],[f60092,f396])).
% 53.15/7.04  fof(f396,plain,(
% 53.15/7.04    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | ~spl6_9),
% 53.15/7.04    inference(avatar_component_clause,[],[f394])).
% 53.15/7.04  fof(f394,plain,(
% 53.15/7.04    spl6_9 <=> sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 53.15/7.04    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 53.15/7.04  fof(f60092,plain,(
% 53.15/7.04    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k2_xboole_0(k1_tarski(sK0),sK1) | (~spl6_74 | ~spl6_75)),
% 53.15/7.04    inference(forward_demodulation,[],[f60091,f155])).
% 53.15/7.04  fof(f155,plain,(
% 53.15/7.04    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 53.15/7.04    inference(forward_demodulation,[],[f153,f55])).
% 53.15/7.04  fof(f55,plain,(
% 53.15/7.04    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 53.15/7.04    inference(cnf_transformation,[],[f10])).
% 53.15/7.04  fof(f10,axiom,(
% 53.15/7.04    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 53.15/7.04  fof(f153,plain,(
% 53.15/7.04    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 53.15/7.04    inference(superposition,[],[f62,f107])).
% 53.15/7.04  fof(f107,plain,(
% 53.15/7.04    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 53.15/7.04    inference(superposition,[],[f105,f55])).
% 53.15/7.04  fof(f105,plain,(
% 53.15/7.04    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 53.15/7.04    inference(resolution,[],[f69,f58])).
% 53.15/7.04  fof(f58,plain,(
% 53.15/7.04    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 53.15/7.04    inference(cnf_transformation,[],[f11])).
% 53.15/7.04  fof(f11,axiom,(
% 53.15/7.04    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 53.15/7.04  fof(f69,plain,(
% 53.15/7.04    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 53.15/7.04    inference(cnf_transformation,[],[f29])).
% 53.15/7.04  fof(f29,plain,(
% 53.15/7.04    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 53.15/7.04    inference(ennf_transformation,[],[f9])).
% 53.15/7.04  fof(f9,axiom,(
% 53.15/7.04    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 53.15/7.04  fof(f62,plain,(
% 53.15/7.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 53.15/7.04    inference(cnf_transformation,[],[f16])).
% 53.15/7.04  fof(f16,axiom,(
% 53.15/7.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 53.15/7.04  fof(f60091,plain,(
% 53.15/7.04    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0) | (~spl6_74 | ~spl6_75)),
% 53.15/7.04    inference(forward_demodulation,[],[f60090,f5856])).
% 53.15/7.04  fof(f5856,plain,(
% 53.15/7.04    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,X2),X2)) )),
% 53.15/7.04    inference(superposition,[],[f5686,f580])).
% 53.15/7.04  fof(f580,plain,(
% 53.15/7.04    ( ! [X12,X13] : (k4_xboole_0(X12,k4_xboole_0(X13,X12)) = X12) )),
% 53.15/7.04    inference(resolution,[],[f575,f75])).
% 53.15/7.04  fof(f75,plain,(
% 53.15/7.04    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 53.15/7.04    inference(cnf_transformation,[],[f45])).
% 53.15/7.04  fof(f45,plain,(
% 53.15/7.04    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 53.15/7.04    inference(nnf_transformation,[],[f14])).
% 53.15/7.04  fof(f14,axiom,(
% 53.15/7.04    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 53.15/7.04  fof(f575,plain,(
% 53.15/7.04    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 53.15/7.04    inference(duplicate_literal_removal,[],[f571])).
% 53.15/7.04  fof(f571,plain,(
% 53.15/7.04    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0)) | r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 53.15/7.04    inference(resolution,[],[f126,f66])).
% 53.15/7.04  fof(f66,plain,(
% 53.15/7.04    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 53.15/7.04    inference(cnf_transformation,[],[f37])).
% 53.15/7.04  fof(f37,plain,(
% 53.15/7.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 53.15/7.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f36])).
% 53.15/7.04  fof(f36,plain,(
% 53.15/7.04    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 53.15/7.04    introduced(choice_axiom,[])).
% 53.15/7.04  fof(f28,plain,(
% 53.15/7.04    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 53.15/7.04    inference(ennf_transformation,[],[f26])).
% 53.15/7.04  fof(f26,plain,(
% 53.15/7.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 53.15/7.04    inference(rectify,[],[f7])).
% 53.15/7.04  fof(f7,axiom,(
% 53.15/7.04    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 53.15/7.04  fof(f126,plain,(
% 53.15/7.04    ( ! [X4,X5,X3] : (~r2_hidden(sK2(X3,k4_xboole_0(X4,X5)),X5) | r1_xboole_0(X3,k4_xboole_0(X4,X5))) )),
% 53.15/7.04    inference(resolution,[],[f95,f67])).
% 53.15/7.04  fof(f67,plain,(
% 53.15/7.04    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 53.15/7.04    inference(cnf_transformation,[],[f37])).
% 53.15/7.04  fof(f95,plain,(
% 53.15/7.04    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 53.15/7.04    inference(equality_resolution,[],[f84])).
% 53.15/7.04  fof(f84,plain,(
% 53.15/7.04    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 53.15/7.04    inference(cnf_transformation,[],[f51])).
% 53.15/7.04  fof(f51,plain,(
% 53.15/7.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 53.15/7.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f49,f50])).
% 53.15/7.04  fof(f50,plain,(
% 53.15/7.04    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 53.15/7.04    introduced(choice_axiom,[])).
% 53.15/7.04  fof(f49,plain,(
% 53.15/7.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 53.15/7.04    inference(rectify,[],[f48])).
% 53.15/7.04  fof(f48,plain,(
% 53.15/7.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 53.15/7.04    inference(flattening,[],[f47])).
% 53.15/7.04  fof(f47,plain,(
% 53.15/7.04    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 53.15/7.04    inference(nnf_transformation,[],[f2])).
% 53.15/7.04  fof(f2,axiom,(
% 53.15/7.04    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 53.15/7.04  fof(f5686,plain,(
% 53.15/7.04    ( ! [X101,X102] : (k1_xboole_0 = k3_xboole_0(X101,k4_xboole_0(X102,X101))) )),
% 53.15/7.04    inference(resolution,[],[f5638,f279])).
% 53.15/7.04  fof(f279,plain,(
% 53.15/7.04    ( ! [X21] : (r2_hidden(sK3(X21,k1_xboole_0),X21) | k1_xboole_0 = X21) )),
% 53.15/7.04    inference(resolution,[],[f70,f129])).
% 53.15/7.04  fof(f129,plain,(
% 53.15/7.04    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 53.15/7.04    inference(condensation,[],[f128])).
% 53.15/7.04  fof(f128,plain,(
% 53.15/7.04    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 53.15/7.04    inference(superposition,[],[f95,f107])).
% 53.15/7.04  fof(f70,plain,(
% 53.15/7.04    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0) | X0 = X1) )),
% 53.15/7.04    inference(cnf_transformation,[],[f40])).
% 53.15/7.04  fof(f40,plain,(
% 53.15/7.04    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 53.15/7.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 53.15/7.04  fof(f39,plain,(
% 53.15/7.04    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 53.15/7.04    introduced(choice_axiom,[])).
% 53.15/7.04  fof(f38,plain,(
% 53.15/7.04    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 53.15/7.04    inference(nnf_transformation,[],[f30])).
% 53.15/7.04  fof(f30,plain,(
% 53.15/7.04    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 53.15/7.04    inference(ennf_transformation,[],[f6])).
% 53.15/7.04  fof(f6,axiom,(
% 53.15/7.04    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 53.15/7.04  fof(f5638,plain,(
% 53.15/7.04    ( ! [X10,X11,X9] : (~r2_hidden(X9,k3_xboole_0(X10,k4_xboole_0(X11,X10)))) )),
% 53.15/7.04    inference(subsumption_resolution,[],[f5622,f4387])).
% 53.15/7.04  fof(f4387,plain,(
% 53.15/7.04    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,X2)) | r2_hidden(X0,X1)) )),
% 53.15/7.04    inference(resolution,[],[f4385,f72])).
% 53.15/7.04  fof(f72,plain,(
% 53.15/7.04    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 53.15/7.04    inference(cnf_transformation,[],[f44])).
% 53.15/7.04  fof(f44,plain,(
% 53.15/7.04    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 53.15/7.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 53.15/7.04  fof(f43,plain,(
% 53.15/7.04    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 53.15/7.04    introduced(choice_axiom,[])).
% 53.15/7.04  fof(f42,plain,(
% 53.15/7.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 53.15/7.04    inference(rectify,[],[f41])).
% 53.15/7.04  fof(f41,plain,(
% 53.15/7.04    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 53.15/7.04    inference(nnf_transformation,[],[f31])).
% 53.15/7.04  fof(f31,plain,(
% 53.15/7.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 53.15/7.04    inference(ennf_transformation,[],[f1])).
% 53.15/7.04  fof(f1,axiom,(
% 53.15/7.04    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 53.15/7.04  fof(f4385,plain,(
% 53.15/7.04    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 53.15/7.04    inference(duplicate_literal_removal,[],[f4368])).
% 53.15/7.04  fof(f4368,plain,(
% 53.15/7.04    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0) | r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 53.15/7.04    inference(resolution,[],[f1111,f74])).
% 53.15/7.04  fof(f74,plain,(
% 53.15/7.04    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 53.15/7.04    inference(cnf_transformation,[],[f44])).
% 53.15/7.04  fof(f1111,plain,(
% 53.15/7.04    ( ! [X6,X7,X5] : (r2_hidden(sK4(k3_xboole_0(X5,X6),X7),X5) | r1_tarski(k3_xboole_0(X5,X6),X7)) )),
% 53.15/7.04    inference(subsumption_resolution,[],[f1097,f96])).
% 53.15/7.04  fof(f96,plain,(
% 53.15/7.04    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 53.15/7.04    inference(equality_resolution,[],[f83])).
% 53.15/7.04  fof(f83,plain,(
% 53.15/7.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 53.15/7.04    inference(cnf_transformation,[],[f51])).
% 53.15/7.04  fof(f1097,plain,(
% 53.15/7.04    ( ! [X6,X7,X5] : (r2_hidden(sK4(k3_xboole_0(X5,X6),X7),k4_xboole_0(X5,X6)) | r2_hidden(sK4(k3_xboole_0(X5,X6),X7),X5) | r1_tarski(k3_xboole_0(X5,X6),X7)) )),
% 53.15/7.04    inference(superposition,[],[f253,f61])).
% 53.15/7.04  fof(f61,plain,(
% 53.15/7.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 53.15/7.04    inference(cnf_transformation,[],[f8])).
% 53.15/7.04  fof(f8,axiom,(
% 53.15/7.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 53.15/7.04  fof(f253,plain,(
% 53.15/7.04    ( ! [X10,X11,X9] : (r2_hidden(sK4(X9,X10),k5_xboole_0(X11,X9)) | r2_hidden(sK4(X9,X10),X11) | r1_tarski(X9,X10)) )),
% 53.15/7.04    inference(resolution,[],[f92,f73])).
% 53.15/7.04  fof(f73,plain,(
% 53.15/7.04    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 53.15/7.04    inference(cnf_transformation,[],[f44])).
% 53.15/7.04  fof(f92,plain,(
% 53.15/7.04    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | r2_hidden(X0,X1) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 53.15/7.04    inference(cnf_transformation,[],[f52])).
% 53.15/7.04  fof(f52,plain,(
% 53.15/7.04    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 53.15/7.04    inference(nnf_transformation,[],[f33])).
% 53.15/7.04  fof(f33,plain,(
% 53.15/7.04    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 53.15/7.04    inference(ennf_transformation,[],[f5])).
% 53.15/7.04  fof(f5,axiom,(
% 53.15/7.04    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 53.15/7.04  fof(f5622,plain,(
% 53.15/7.04    ( ! [X10,X11,X9] : (~r2_hidden(X9,X10) | ~r2_hidden(X9,k3_xboole_0(X10,k4_xboole_0(X11,X10)))) )),
% 53.15/7.04    inference(resolution,[],[f5520,f68])).
% 53.15/7.04  fof(f68,plain,(
% 53.15/7.04    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 53.15/7.04    inference(cnf_transformation,[],[f37])).
% 53.15/7.04  fof(f5520,plain,(
% 53.15/7.04    ( ! [X4,X5] : (r1_xboole_0(k3_xboole_0(X4,k4_xboole_0(X5,X4)),X4)) )),
% 53.15/7.04    inference(resolution,[],[f5338,f81])).
% 53.15/7.04  fof(f81,plain,(
% 53.15/7.04    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 53.15/7.04    inference(cnf_transformation,[],[f32])).
% 53.15/7.04  fof(f32,plain,(
% 53.15/7.04    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 53.15/7.04    inference(ennf_transformation,[],[f13])).
% 53.15/7.04  fof(f13,axiom,(
% 53.15/7.04    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 53.15/7.04  fof(f5338,plain,(
% 53.15/7.04    ( ! [X134,X135] : (r1_xboole_0(k3_xboole_0(X134,k4_xboole_0(X135,X134)),k2_xboole_0(X134,X135))) )),
% 53.15/7.04    inference(subsumption_resolution,[],[f5311,f67])).
% 53.15/7.04  fof(f5311,plain,(
% 53.15/7.04    ( ! [X134,X135] : (~r2_hidden(sK2(k3_xboole_0(X134,k4_xboole_0(X135,X134)),k2_xboole_0(X134,X135)),k2_xboole_0(X134,X135)) | r1_xboole_0(k3_xboole_0(X134,k4_xboole_0(X135,X134)),k2_xboole_0(X134,X135))) )),
% 53.15/7.04    inference(superposition,[],[f841,f5212])).
% 53.15/7.04  fof(f5212,plain,(
% 53.15/7.04    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(k2_xboole_0(X2,X3),k3_xboole_0(X2,k4_xboole_0(X3,X2)))) )),
% 53.15/7.04    inference(backward_demodulation,[],[f206,f2056])).
% 53.15/7.04  fof(f2056,plain,(
% 53.15/7.04    ( ! [X8,X7] : (k2_xboole_0(X8,X7) = k2_xboole_0(X8,k4_xboole_0(X7,X8))) )),
% 53.15/7.04    inference(forward_demodulation,[],[f2007,f62])).
% 53.15/7.04  fof(f2007,plain,(
% 53.15/7.04    ( ! [X8,X7] : (k2_xboole_0(X8,k4_xboole_0(X7,X8)) = k5_xboole_0(X8,k4_xboole_0(X7,X8))) )),
% 53.15/7.04    inference(superposition,[],[f62,f562])).
% 53.15/7.04  fof(f562,plain,(
% 53.15/7.04    ( ! [X12,X13] : (k4_xboole_0(X12,X13) = k4_xboole_0(k4_xboole_0(X12,X13),X13)) )),
% 53.15/7.04    inference(resolution,[],[f557,f75])).
% 53.15/7.04  fof(f557,plain,(
% 53.15/7.04    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 53.15/7.04    inference(duplicate_literal_removal,[],[f553])).
% 53.15/7.04  fof(f553,plain,(
% 53.15/7.04    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1) | r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 53.15/7.04    inference(resolution,[],[f125,f67])).
% 53.15/7.04  fof(f125,plain,(
% 53.15/7.04    ( ! [X2,X0,X1] : (~r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X1) | r1_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 53.15/7.04    inference(resolution,[],[f95,f66])).
% 53.15/7.04  fof(f206,plain,(
% 53.15/7.04    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k5_xboole_0(k2_xboole_0(X2,X3),k3_xboole_0(X2,k4_xboole_0(X3,X2)))) )),
% 53.15/7.04    inference(superposition,[],[f65,f62])).
% 53.15/7.04  fof(f65,plain,(
% 53.15/7.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 53.15/7.04    inference(cnf_transformation,[],[f15])).
% 53.15/7.04  fof(f15,axiom,(
% 53.15/7.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 53.15/7.04  fof(f841,plain,(
% 53.15/7.04    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),k5_xboole_0(X1,X0)) | r1_xboole_0(X0,X1)) )),
% 53.15/7.04    inference(duplicate_literal_removal,[],[f832])).
% 53.15/7.04  fof(f832,plain,(
% 53.15/7.04    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),k5_xboole_0(X1,X0)) | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 53.15/7.04    inference(resolution,[],[f241,f66])).
% 53.15/7.04  fof(f241,plain,(
% 53.15/7.04    ( ! [X6,X8,X7] : (~r2_hidden(sK2(X6,X7),X8) | ~r2_hidden(sK2(X6,X7),k5_xboole_0(X7,X8)) | r1_xboole_0(X6,X7)) )),
% 53.15/7.04    inference(resolution,[],[f90,f67])).
% 53.15/7.04  fof(f90,plain,(
% 53.15/7.04    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,X2) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 53.15/7.04    inference(cnf_transformation,[],[f52])).
% 53.15/7.04  fof(f60090,plain,(
% 53.15/7.04    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k3_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))) | (~spl6_74 | ~spl6_75)),
% 53.15/7.04    inference(forward_demodulation,[],[f59779,f45062])).
% 53.15/7.04  fof(f45062,plain,(
% 53.15/7.04    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) | ~spl6_74),
% 53.15/7.04    inference(avatar_component_clause,[],[f45060])).
% 53.15/7.04  fof(f45060,plain,(
% 53.15/7.04    spl6_74 <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 53.15/7.04    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 53.15/7.04  fof(f59779,plain,(
% 53.15/7.04    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),sK1)) = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k3_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(k1_tarski(sK0),sK1))) | ~spl6_75),
% 53.15/7.04    inference(superposition,[],[f209,f58236])).
% 53.15/7.04  fof(f58236,plain,(
% 53.15/7.04    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),sK1) | ~spl6_75),
% 53.15/7.04    inference(avatar_component_clause,[],[f58234])).
% 53.15/7.04  fof(f58234,plain,(
% 53.15/7.04    spl6_75 <=> k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),sK1)),
% 53.15/7.04    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).
% 53.15/7.04  fof(f209,plain,(
% 53.15/7.04    ( ! [X6,X7] : (k2_xboole_0(k5_xboole_0(X6,X7),k3_xboole_0(X6,X7)) = k5_xboole_0(k2_xboole_0(X6,X7),k3_xboole_0(k5_xboole_0(X6,X7),k3_xboole_0(X6,X7)))) )),
% 53.15/7.04    inference(superposition,[],[f65,f65])).
% 53.15/7.04  fof(f59573,plain,(
% 53.15/7.04    spl6_75 | ~spl6_53),
% 53.15/7.04    inference(avatar_split_clause,[],[f38625,f10261,f58234])).
% 53.15/7.04  fof(f10261,plain,(
% 53.15/7.04    spl6_53 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 53.15/7.04    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 53.15/7.04  fof(f38625,plain,(
% 53.15/7.04    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),sK1) | ~spl6_53),
% 53.15/7.04    inference(forward_demodulation,[],[f38624,f147])).
% 53.15/7.04  fof(f147,plain,(
% 53.15/7.04    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 53.15/7.04    inference(resolution,[],[f132,f69])).
% 53.15/7.04  fof(f132,plain,(
% 53.15/7.04    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 53.15/7.04    inference(resolution,[],[f129,f73])).
% 53.15/7.04  fof(f38624,plain,(
% 53.15/7.04    k5_xboole_0(k1_tarski(sK0),sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k1_tarski(sK0))) | ~spl6_53),
% 53.15/7.04    inference(forward_demodulation,[],[f38504,f146])).
% 53.15/7.04  fof(f146,plain,(
% 53.15/7.04    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 53.15/7.04    inference(resolution,[],[f131,f75])).
% 53.15/7.04  fof(f131,plain,(
% 53.15/7.04    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) )),
% 53.15/7.04    inference(resolution,[],[f129,f67])).
% 53.15/7.04  fof(f38504,plain,(
% 53.15/7.04    k5_xboole_0(k1_tarski(sK0),sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_xboole_0)) | ~spl6_53),
% 53.15/7.04    inference(superposition,[],[f38480,f10263])).
% 53.15/7.04  fof(f10263,plain,(
% 53.15/7.04    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | ~spl6_53),
% 53.15/7.04    inference(avatar_component_clause,[],[f10261])).
% 53.15/7.04  fof(f38480,plain,(
% 53.15/7.04    ( ! [X4,X5] : (k5_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,X5)))) )),
% 53.15/7.04    inference(forward_demodulation,[],[f38479,f155])).
% 53.15/7.04  fof(f38479,plain,(
% 53.15/7.04    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,X5))) = k5_xboole_0(k5_xboole_0(X4,X5),k1_xboole_0)) )),
% 53.15/7.04    inference(forward_demodulation,[],[f748,f5686])).
% 53.15/7.04  fof(f748,plain,(
% 53.15/7.04    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,X5))) = k5_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,X5))))) )),
% 53.15/7.04    inference(superposition,[],[f206,f64])).
% 53.15/7.04  fof(f64,plain,(
% 53.15/7.04    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 53.15/7.04    inference(cnf_transformation,[],[f3])).
% 53.15/7.04  fof(f3,axiom,(
% 53.15/7.04    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 53.15/7.04  fof(f45063,plain,(
% 53.15/7.04    spl6_74 | ~spl6_9),
% 53.15/7.04    inference(avatar_split_clause,[],[f44596,f394,f45060])).
% 53.15/7.04  fof(f44596,plain,(
% 53.15/7.04    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) | ~spl6_9),
% 53.15/7.04    inference(superposition,[],[f44287,f396])).
% 53.15/7.04  fof(f44287,plain,(
% 53.15/7.04    ( ! [X4,X3] : (k3_xboole_0(X3,k2_xboole_0(X3,X4)) = X3) )),
% 53.15/7.04    inference(superposition,[],[f11628,f55])).
% 53.15/7.04  fof(f11628,plain,(
% 53.15/7.04    ( ! [X54,X55] : (k2_xboole_0(k3_xboole_0(X54,k2_xboole_0(X54,X55)),k1_xboole_0) = X54) )),
% 53.15/7.04    inference(superposition,[],[f63,f11272])).
% 53.15/7.04  fof(f11272,plain,(
% 53.15/7.04    ( ! [X196,X197] : (k1_xboole_0 = k4_xboole_0(X196,k2_xboole_0(X196,X197))) )),
% 53.15/7.04    inference(resolution,[],[f9968,f279])).
% 53.15/7.04  fof(f9968,plain,(
% 53.15/7.04    ( ! [X10,X11,X9] : (~r2_hidden(X9,k4_xboole_0(X10,k2_xboole_0(X10,X11)))) )),
% 53.15/7.04    inference(subsumption_resolution,[],[f9952,f96])).
% 53.15/7.04  fof(f9952,plain,(
% 53.15/7.04    ( ! [X10,X11,X9] : (~r2_hidden(X9,k4_xboole_0(X10,k2_xboole_0(X10,X11))) | ~r2_hidden(X9,X10)) )),
% 53.15/7.04    inference(resolution,[],[f9888,f68])).
% 53.15/7.04  fof(f9888,plain,(
% 53.15/7.04    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))) )),
% 53.15/7.04    inference(superposition,[],[f8208,f62])).
% 53.15/7.04  fof(f8208,plain,(
% 53.15/7.04    ( ! [X6,X4,X5] : (r1_xboole_0(X6,k4_xboole_0(X4,k5_xboole_0(X6,k4_xboole_0(X5,X4))))) )),
% 53.15/7.04    inference(superposition,[],[f7843,f580])).
% 53.15/7.04  fof(f7843,plain,(
% 53.15/7.04    ( ! [X8,X7,X9] : (r1_xboole_0(X7,k4_xboole_0(k4_xboole_0(X8,X9),k5_xboole_0(X7,X9)))) )),
% 53.15/7.04    inference(duplicate_literal_removal,[],[f7808])).
% 53.15/7.04  fof(f7808,plain,(
% 53.15/7.04    ( ! [X8,X7,X9] : (r1_xboole_0(X7,k4_xboole_0(k4_xboole_0(X8,X9),k5_xboole_0(X7,X9))) | r1_xboole_0(X7,k4_xboole_0(k4_xboole_0(X8,X9),k5_xboole_0(X7,X9)))) )),
% 53.15/7.04    inference(resolution,[],[f912,f625])).
% 53.15/7.04  fof(f625,plain,(
% 53.15/7.04    ( ! [X30,X28,X31,X29] : (~r2_hidden(sK2(X28,k4_xboole_0(k4_xboole_0(X29,X30),X31)),X30) | r1_xboole_0(X28,k4_xboole_0(k4_xboole_0(X29,X30),X31))) )),
% 53.15/7.04    inference(resolution,[],[f134,f95])).
% 53.15/7.04  fof(f134,plain,(
% 53.15/7.04    ( ! [X4,X5,X3] : (r2_hidden(sK2(X3,k4_xboole_0(X4,X5)),X4) | r1_xboole_0(X3,k4_xboole_0(X4,X5))) )),
% 53.15/7.04    inference(resolution,[],[f96,f67])).
% 53.15/7.04  fof(f912,plain,(
% 53.15/7.04    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,k4_xboole_0(X1,k5_xboole_0(X0,X2))),X2) | r1_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,X2)))) )),
% 53.15/7.04    inference(duplicate_literal_removal,[],[f890])).
% 53.15/7.04  fof(f890,plain,(
% 53.15/7.04    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,k4_xboole_0(X1,k5_xboole_0(X0,X2))),X2) | r1_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,X2))) | r1_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(X0,X2)))) )),
% 53.15/7.04    inference(resolution,[],[f245,f126])).
% 53.15/7.04  fof(f245,plain,(
% 53.15/7.04    ( ! [X4,X5,X3] : (r2_hidden(sK2(X3,X4),k5_xboole_0(X3,X5)) | r2_hidden(sK2(X3,X4),X5) | r1_xboole_0(X3,X4)) )),
% 53.15/7.04    inference(resolution,[],[f91,f66])).
% 53.15/7.04  fof(f91,plain,(
% 53.15/7.04    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,X2) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 53.15/7.04    inference(cnf_transformation,[],[f52])).
% 53.15/7.04  fof(f63,plain,(
% 53.15/7.04    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 53.15/7.04    inference(cnf_transformation,[],[f12])).
% 53.15/7.04  fof(f12,axiom,(
% 53.15/7.04    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 53.15/7.04  fof(f10369,plain,(
% 53.15/7.04    spl6_53 | ~spl6_50),
% 53.15/7.04    inference(avatar_split_clause,[],[f10220,f10084,f10261])).
% 53.15/7.04  fof(f10084,plain,(
% 53.15/7.04    spl6_50 <=> ! [X3] : ~r2_hidden(X3,k4_xboole_0(k1_tarski(sK0),sK1))),
% 53.15/7.04    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 53.15/7.04  fof(f10220,plain,(
% 53.15/7.04    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) | ~spl6_50),
% 53.15/7.04    inference(resolution,[],[f10085,f2152])).
% 53.15/7.04  fof(f2152,plain,(
% 53.15/7.04    ( ! [X4,X5] : (r2_hidden(sK5(k1_xboole_0,X4,X5),X5) | k1_xboole_0 = X5) )),
% 53.15/7.04    inference(forward_demodulation,[],[f2151,f507])).
% 53.15/7.04  fof(f507,plain,(
% 53.15/7.04    ( ! [X26] : (k1_xboole_0 = k4_xboole_0(X26,X26)) )),
% 53.15/7.04    inference(resolution,[],[f325,f129])).
% 53.15/7.04  fof(f325,plain,(
% 53.15/7.04    ( ! [X0,X1] : (r2_hidden(sK5(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1) )),
% 53.15/7.04    inference(duplicate_literal_removal,[],[f322])).
% 53.15/7.04  fof(f322,plain,(
% 53.15/7.04    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = X1 | r2_hidden(sK5(X0,X0,X1),X1) | r2_hidden(sK5(X0,X0,X1),X1) | k4_xboole_0(X0,X0) = X1) )),
% 53.15/7.04    inference(resolution,[],[f87,f86])).
% 53.15/7.04  fof(f86,plain,(
% 53.15/7.04    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X0) | r2_hidden(sK5(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 53.15/7.04    inference(cnf_transformation,[],[f51])).
% 53.15/7.04  fof(f87,plain,(
% 53.15/7.04    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 53.15/7.04    inference(cnf_transformation,[],[f51])).
% 53.15/7.04  fof(f2151,plain,(
% 53.15/7.04    ( ! [X4,X5,X3] : (k1_xboole_0 = X5 | r2_hidden(sK5(k4_xboole_0(X3,X3),X4,X5),X5)) )),
% 53.15/7.04    inference(forward_demodulation,[],[f2150,f107])).
% 53.15/7.04  fof(f2150,plain,(
% 53.15/7.04    ( ! [X4,X5,X3] : (k4_xboole_0(k1_xboole_0,X4) = X5 | r2_hidden(sK5(k4_xboole_0(X3,X3),X4,X5),X5)) )),
% 53.15/7.04    inference(forward_demodulation,[],[f2148,f507])).
% 53.15/7.04  fof(f2148,plain,(
% 53.15/7.04    ( ! [X4,X5,X3] : (k4_xboole_0(k4_xboole_0(X3,X3),X4) = X5 | r2_hidden(sK5(k4_xboole_0(X3,X3),X4,X5),X5)) )),
% 53.15/7.04    inference(duplicate_literal_removal,[],[f2138])).
% 53.15/7.04  fof(f2138,plain,(
% 53.15/7.04    ( ! [X4,X5,X3] : (k4_xboole_0(k4_xboole_0(X3,X3),X4) = X5 | r2_hidden(sK5(k4_xboole_0(X3,X3),X4,X5),X5) | r2_hidden(sK5(k4_xboole_0(X3,X3),X4,X5),X5) | k4_xboole_0(k4_xboole_0(X3,X3),X4) = X5) )),
% 53.15/7.04    inference(resolution,[],[f306,f305])).
% 53.15/7.04  fof(f305,plain,(
% 53.15/7.04    ( ! [X19,X17,X18,X16] : (r2_hidden(sK5(k4_xboole_0(X16,X17),X18,X19),X19) | r2_hidden(sK5(k4_xboole_0(X16,X17),X18,X19),X16) | k4_xboole_0(k4_xboole_0(X16,X17),X18) = X19) )),
% 53.15/7.04    inference(resolution,[],[f86,f96])).
% 53.15/7.04  fof(f306,plain,(
% 53.15/7.04    ( ! [X23,X21,X22,X20] : (~r2_hidden(sK5(k4_xboole_0(X20,X21),X22,X23),X21) | k4_xboole_0(k4_xboole_0(X20,X21),X22) = X23 | r2_hidden(sK5(k4_xboole_0(X20,X21),X22,X23),X23)) )),
% 53.15/7.04    inference(resolution,[],[f86,f95])).
% 53.15/7.04  fof(f10085,plain,(
% 53.15/7.04    ( ! [X3] : (~r2_hidden(X3,k4_xboole_0(k1_tarski(sK0),sK1))) ) | ~spl6_50),
% 53.15/7.04    inference(avatar_component_clause,[],[f10084])).
% 53.15/7.04  fof(f10086,plain,(
% 53.15/7.04    spl6_50 | ~spl6_49),
% 53.15/7.04    inference(avatar_split_clause,[],[f10029,f9995,f10084])).
% 53.15/7.04  fof(f9995,plain,(
% 53.15/7.04    spl6_49 <=> r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),sK1))),
% 53.15/7.04    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 53.15/7.04  fof(f10029,plain,(
% 53.15/7.04    ( ! [X3] : (~r2_hidden(X3,k4_xboole_0(k1_tarski(sK0),sK1))) ) | ~spl6_49),
% 53.15/7.04    inference(subsumption_resolution,[],[f10027,f96])).
% 53.15/7.04  fof(f10027,plain,(
% 53.15/7.04    ( ! [X3] : (~r2_hidden(X3,k4_xboole_0(k1_tarski(sK0),sK1)) | ~r2_hidden(X3,k1_tarski(sK0))) ) | ~spl6_49),
% 53.15/7.04    inference(resolution,[],[f9997,f68])).
% 53.15/7.04  fof(f9997,plain,(
% 53.15/7.04    r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),sK1)) | ~spl6_49),
% 53.15/7.04    inference(avatar_component_clause,[],[f9995])).
% 53.15/7.04  fof(f9998,plain,(
% 53.15/7.04    spl6_49 | ~spl6_9),
% 53.15/7.04    inference(avatar_split_clause,[],[f9964,f394,f9995])).
% 53.15/7.04  fof(f9964,plain,(
% 53.15/7.04    r1_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),sK1)) | ~spl6_9),
% 53.15/7.04    inference(superposition,[],[f9888,f396])).
% 53.15/7.04  fof(f397,plain,(
% 53.15/7.04    spl6_9 | ~spl6_1),
% 53.15/7.04    inference(avatar_split_clause,[],[f382,f98,f394])).
% 53.15/7.04  fof(f98,plain,(
% 53.15/7.04    spl6_1 <=> r2_hidden(sK0,sK1)),
% 53.15/7.04    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 53.15/7.04  fof(f382,plain,(
% 53.15/7.04    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) | ~spl6_1),
% 53.15/7.04    inference(resolution,[],[f106,f100])).
% 53.15/7.04  fof(f100,plain,(
% 53.15/7.04    r2_hidden(sK0,sK1) | ~spl6_1),
% 53.15/7.04    inference(avatar_component_clause,[],[f98])).
% 53.15/7.04  fof(f106,plain,(
% 53.15/7.04    ( ! [X2,X3] : (~r2_hidden(X2,X3) | k2_xboole_0(k1_tarski(X2),X3) = X3) )),
% 53.15/7.04    inference(resolution,[],[f69,f78])).
% 53.15/7.04  fof(f78,plain,(
% 53.15/7.04    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 53.15/7.04    inference(cnf_transformation,[],[f46])).
% 53.15/7.04  fof(f46,plain,(
% 53.15/7.04    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 53.15/7.04    inference(nnf_transformation,[],[f21])).
% 53.15/7.04  fof(f21,axiom,(
% 53.15/7.04    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 53.15/7.04  fof(f145,plain,(
% 53.15/7.04    ~spl6_2),
% 53.15/7.04    inference(avatar_split_clause,[],[f54,f142])).
% 53.15/7.04  fof(f54,plain,(
% 53.15/7.04    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 53.15/7.04    inference(cnf_transformation,[],[f35])).
% 53.15/7.04  fof(f35,plain,(
% 53.15/7.04    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 53.15/7.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f34])).
% 53.15/7.04  fof(f34,plain,(
% 53.15/7.04    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 53.15/7.04    introduced(choice_axiom,[])).
% 53.15/7.04  fof(f27,plain,(
% 53.15/7.04    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 53.15/7.04    inference(ennf_transformation,[],[f24])).
% 53.15/7.04  fof(f24,negated_conjecture,(
% 53.15/7.04    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 53.15/7.04    inference(negated_conjecture,[],[f23])).
% 53.15/7.04  fof(f23,conjecture,(
% 53.15/7.04    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 53.15/7.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 53.15/7.04  fof(f101,plain,(
% 53.15/7.04    spl6_1),
% 53.15/7.04    inference(avatar_split_clause,[],[f53,f98])).
% 53.15/7.04  fof(f53,plain,(
% 53.15/7.04    r2_hidden(sK0,sK1)),
% 53.15/7.04    inference(cnf_transformation,[],[f35])).
% 53.15/7.04  % SZS output end Proof for theBenchmark
% 53.15/7.04  % (17593)------------------------------
% 53.15/7.04  % (17593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 53.15/7.04  % (17593)Termination reason: Refutation
% 53.15/7.04  
% 53.15/7.04  % (17593)Memory used [KB]: 45287
% 53.15/7.04  % (17593)Time elapsed: 4.947 s
% 53.15/7.04  % (17593)------------------------------
% 53.15/7.04  % (17593)------------------------------
% 53.15/7.05  % (17280)Success in time 6.69 s
%------------------------------------------------------------------------------
