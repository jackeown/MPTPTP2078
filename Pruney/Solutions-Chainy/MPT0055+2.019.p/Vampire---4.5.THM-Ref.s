%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:07 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 280 expanded)
%              Number of leaves         :   20 (  85 expanded)
%              Depth                    :   20
%              Number of atoms          :  267 ( 807 expanded)
%              Number of equality atoms :   74 ( 218 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f3272,f3380])).

fof(f3380,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f3379])).

fof(f3379,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f76,f2732])).

fof(f2732,plain,(
    ! [X6] : r1_xboole_0(X6,k1_xboole_0) ),
    inference(superposition,[],[f2682,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f39,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2682,plain,(
    ! [X8,X9] : r1_xboole_0(X8,k3_xboole_0(X9,k4_xboole_0(X9,X8))) ),
    inference(resolution,[],[f695,f688])).

fof(f688,plain,(
    ! [X4,X3] : r1_xboole_0(k3_xboole_0(X4,X3),k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f628,f95])).

fof(f95,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f41,f39])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f628,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(duplicate_literal_removal,[],[f617])).

fof(f617,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X0))
      | r1_xboole_0(X0,k4_xboole_0(X1,X0)) ) ),
    inference(resolution,[],[f86,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
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

fof(f86,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK3(X3,k4_xboole_0(X4,X5)),X5)
      | r1_xboole_0(X3,k4_xboole_0(X4,X5)) ) ),
    inference(resolution,[],[f56,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f695,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X2)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f147,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f147,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ r2_hidden(X13,k3_xboole_0(X10,k3_xboole_0(X11,X12)))
      | ~ r1_xboole_0(k3_xboole_0(X10,X11),X12) ) ),
    inference(superposition,[],[f44,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,
    ( ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_1
  <=> ! [X0] : ~ r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f3272,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f3271])).

fof(f3271,plain,
    ( $false
    | ~ spl5_2 ),
    inference(trivial_inequality_removal,[],[f3270])).

fof(f3270,plain,
    ( k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1)
    | ~ spl5_2 ),
    inference(superposition,[],[f33,f2923])).

fof(f2923,plain,
    ( ! [X4,X5] : k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f340,f2922])).

fof(f2922,plain,
    ( ! [X50,X48,X49] : k3_xboole_0(X50,X48) = k4_xboole_0(k3_xboole_0(X50,X48),k4_xboole_0(X49,X48))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f2921,f36])).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f2921,plain,
    ( ! [X50,X48,X49] : k4_xboole_0(k3_xboole_0(X50,X48),k1_xboole_0) = k4_xboole_0(k3_xboole_0(X50,X48),k4_xboole_0(X49,X48))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f2836,f34])).

fof(f2836,plain,
    ( ! [X50,X48,X49] : k4_xboole_0(k3_xboole_0(X50,X48),k3_xboole_0(X50,k1_xboole_0)) = k4_xboole_0(k3_xboole_0(X50,X48),k4_xboole_0(X49,X48))
    | ~ spl5_2 ),
    inference(superposition,[],[f146,f2323])).

fof(f2323,plain,
    ( ! [X10,X11] : k1_xboole_0 = k3_xboole_0(X10,k4_xboole_0(X11,X10))
    | ~ spl5_2 ),
    inference(resolution,[],[f1439,f1297])).

fof(f1297,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f1081,f37])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f1081,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = k1_xboole_0
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(forward_demodulation,[],[f1080,f120])).

fof(f120,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(X7,X7) ),
    inference(backward_demodulation,[],[f104,f119])).

fof(f119,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f115,f36])).

fof(f115,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f41,f62])).

fof(f104,plain,(
    ! [X7] : k4_xboole_0(k1_xboole_0,X7) = k4_xboole_0(X7,X7) ),
    inference(superposition,[],[f42,f58])).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f38,f35])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1080,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k4_xboole_0(X0,X0)
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(subsumption_resolution,[],[f1079,f44])).

fof(f1079,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k4_xboole_0(X0,X0)
      | ~ r1_xboole_0(X1,X2)
      | r2_hidden(sK4(X0,X0,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X2)) ) ),
    inference(duplicate_literal_removal,[],[f1057])).

fof(f1057,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k4_xboole_0(X0,X0)
      | ~ r1_xboole_0(X1,X2)
      | k3_xboole_0(X1,X2) = k4_xboole_0(X0,X0)
      | r2_hidden(sK4(X0,X0,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f167,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f167,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,k3_xboole_0(X2,X3)),X0)
      | k4_xboole_0(X0,X1) = k3_xboole_0(X2,X3)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f52,f44])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1439,plain,
    ( ! [X6,X8,X7] : r1_xboole_0(k3_xboole_0(X6,k4_xboole_0(X7,X6)),X8)
    | ~ spl5_2 ),
    inference(resolution,[],[f1412,f45])).

fof(f1412,plain,
    ( ! [X24,X23,X25] : ~ r2_hidden(X25,k3_xboole_0(X24,k4_xboole_0(X23,X24)))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f1411,f39])).

fof(f1411,plain,
    ( ! [X24,X23,X25] : ~ r2_hidden(X25,k3_xboole_0(k4_xboole_0(X23,X24),X24))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f1392,f320])).

fof(f320,plain,
    ( ! [X4,X5,X3] :
        ( r2_hidden(X5,X3)
        | ~ r2_hidden(X5,k3_xboole_0(X3,X4)) )
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f315,f79])).

fof(f79,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_2
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f315,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X5,k1_xboole_0)
      | r2_hidden(X5,X3)
      | ~ r2_hidden(X5,k3_xboole_0(X3,X4)) ) ),
    inference(superposition,[],[f55,f287])).

fof(f287,plain,(
    ! [X24,X23] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X23,X24),X23) ),
    inference(forward_demodulation,[],[f281,f120])).

fof(f281,plain,(
    ! [X24,X23] : k4_xboole_0(k3_xboole_0(X23,X24),X23) = k4_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X23,X24)) ),
    inference(superposition,[],[f95,f134])).

fof(f134,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f48,f37])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1392,plain,(
    ! [X24,X23,X25] :
      ( ~ r2_hidden(X25,k4_xboole_0(X23,X24))
      | ~ r2_hidden(X25,k3_xboole_0(k4_xboole_0(X23,X24),X24)) ) ),
    inference(superposition,[],[f99,f241])).

fof(f241,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k4_xboole_0(k4_xboole_0(X6,X5),X5) ),
    inference(forward_demodulation,[],[f233,f101])).

fof(f101,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f42,f38])).

fof(f233,plain,(
    ! [X6,X5] : k4_xboole_0(k4_xboole_0(X6,X5),X5) = k4_xboole_0(k2_xboole_0(X5,X6),X5) ),
    inference(superposition,[],[f101,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f99,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,k4_xboole_0(X5,X6))
      | ~ r2_hidden(X7,k3_xboole_0(X5,X6)) ) ),
    inference(superposition,[],[f56,f41])).

fof(f146,plain,(
    ! [X8,X7,X9] : k4_xboole_0(k3_xboole_0(X7,X8),X9) = k4_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k3_xboole_0(X8,X9))) ),
    inference(superposition,[],[f41,f48])).

fof(f340,plain,(
    ! [X4,X5] : k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f42,f322])).

fof(f322,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f100,f321])).

fof(f321,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6 ),
    inference(forward_demodulation,[],[f316,f35])).

fof(f316,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k1_xboole_0) = k2_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f40,f287])).

fof(f100,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f97,f38])).

fof(f97,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f40,f41])).

fof(f33,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f80,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f70,f78,f75])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f44,f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:54:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (24005)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (23999)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (23999)Refutation not found, incomplete strategy% (23999)------------------------------
% 0.20/0.48  % (23999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23999)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (23999)Memory used [KB]: 6140
% 0.20/0.48  % (23999)Time elapsed: 0.061 s
% 0.20/0.48  % (23999)------------------------------
% 0.20/0.48  % (23999)------------------------------
% 0.20/0.49  % (24007)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.49  % (24013)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  % (24003)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.51  % (24019)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (24008)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.52  % (24009)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  % (24011)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (24011)Refutation not found, incomplete strategy% (24011)------------------------------
% 0.20/0.52  % (24011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24015)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.52  % (24006)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.52  % (24014)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.52  % (24010)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.52  % (24017)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.52  % (24014)Refutation not found, incomplete strategy% (24014)------------------------------
% 0.20/0.52  % (24014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24014)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24014)Memory used [KB]: 6140
% 0.20/0.52  % (24014)Time elapsed: 0.059 s
% 0.20/0.52  % (24014)------------------------------
% 0.20/0.52  % (24014)------------------------------
% 0.20/0.52  % (24002)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (24009)Refutation not found, incomplete strategy% (24009)------------------------------
% 0.20/0.52  % (24009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24009)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24009)Memory used [KB]: 6012
% 0.20/0.52  % (24009)Time elapsed: 0.108 s
% 0.20/0.52  % (24009)------------------------------
% 0.20/0.52  % (24009)------------------------------
% 0.20/0.52  % (24002)Refutation not found, incomplete strategy% (24002)------------------------------
% 0.20/0.52  % (24002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24002)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (24002)Memory used [KB]: 10618
% 0.20/0.52  % (24002)Time elapsed: 0.108 s
% 0.20/0.52  % (24002)------------------------------
% 0.20/0.52  % (24002)------------------------------
% 0.20/0.52  % (24004)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (24001)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.53  % (24019)Refutation not found, incomplete strategy% (24019)------------------------------
% 0.20/0.53  % (24019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24019)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24019)Memory used [KB]: 10618
% 0.20/0.53  % (24019)Time elapsed: 0.114 s
% 0.20/0.53  % (24019)------------------------------
% 0.20/0.53  % (24019)------------------------------
% 0.20/0.53  % (24018)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.53  % (24011)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (24011)Memory used [KB]: 6012
% 0.20/0.53  % (24011)Time elapsed: 0.003 s
% 0.20/0.53  % (24011)------------------------------
% 0.20/0.53  % (24011)------------------------------
% 1.35/0.53  % (24016)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.35/0.53  % (24000)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.53  % (24000)Refutation not found, incomplete strategy% (24000)------------------------------
% 1.35/0.53  % (24000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (24000)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (24000)Memory used [KB]: 10618
% 1.35/0.53  % (24000)Time elapsed: 0.119 s
% 1.35/0.53  % (24000)------------------------------
% 1.35/0.53  % (24000)------------------------------
% 1.35/0.54  % (24010)Refutation not found, incomplete strategy% (24010)------------------------------
% 1.35/0.54  % (24010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (24010)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (24010)Memory used [KB]: 10618
% 1.35/0.54  % (24010)Time elapsed: 0.122 s
% 1.35/0.54  % (24010)------------------------------
% 1.35/0.54  % (24010)------------------------------
% 1.53/0.55  % (24012)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.53/0.55  % (24012)Refutation not found, incomplete strategy% (24012)------------------------------
% 1.53/0.55  % (24012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.55  % (24012)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.55  
% 1.53/0.55  % (24012)Memory used [KB]: 1663
% 1.53/0.55  % (24012)Time elapsed: 0.096 s
% 1.53/0.55  % (24012)------------------------------
% 1.53/0.55  % (24012)------------------------------
% 1.53/0.62  % (24001)Refutation found. Thanks to Tanya!
% 1.53/0.62  % SZS status Theorem for theBenchmark
% 1.53/0.62  % SZS output start Proof for theBenchmark
% 1.53/0.62  fof(f3381,plain,(
% 1.53/0.62    $false),
% 1.53/0.62    inference(avatar_sat_refutation,[],[f80,f3272,f3380])).
% 1.53/0.62  fof(f3380,plain,(
% 1.53/0.62    ~spl5_1),
% 1.53/0.62    inference(avatar_contradiction_clause,[],[f3379])).
% 1.53/0.62  fof(f3379,plain,(
% 1.53/0.62    $false | ~spl5_1),
% 1.53/0.62    inference(subsumption_resolution,[],[f76,f2732])).
% 1.53/0.62  fof(f2732,plain,(
% 1.53/0.62    ( ! [X6] : (r1_xboole_0(X6,k1_xboole_0)) )),
% 1.53/0.62    inference(superposition,[],[f2682,f62])).
% 1.53/0.62  fof(f62,plain,(
% 1.53/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.53/0.62    inference(superposition,[],[f39,f34])).
% 1.53/0.62  fof(f34,plain,(
% 1.53/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f9])).
% 1.53/0.62  fof(f9,axiom,(
% 1.53/0.62    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.53/0.62  fof(f39,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f2])).
% 1.53/0.62  fof(f2,axiom,(
% 1.53/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.53/0.62  fof(f2682,plain,(
% 1.53/0.62    ( ! [X8,X9] : (r1_xboole_0(X8,k3_xboole_0(X9,k4_xboole_0(X9,X8)))) )),
% 1.53/0.62    inference(resolution,[],[f695,f688])).
% 1.53/0.62  fof(f688,plain,(
% 1.53/0.62    ( ! [X4,X3] : (r1_xboole_0(k3_xboole_0(X4,X3),k4_xboole_0(X3,X4))) )),
% 1.53/0.62    inference(superposition,[],[f628,f95])).
% 1.53/0.62  fof(f95,plain,(
% 1.53/0.62    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X3,X2))) )),
% 1.53/0.62    inference(superposition,[],[f41,f39])).
% 1.53/0.62  fof(f41,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.53/0.62    inference(cnf_transformation,[],[f13])).
% 1.53/0.62  fof(f13,axiom,(
% 1.53/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.53/0.62  fof(f628,plain,(
% 1.53/0.62    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.53/0.62    inference(duplicate_literal_removal,[],[f617])).
% 1.53/0.62  fof(f617,plain,(
% 1.53/0.62    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0)) | r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.53/0.62    inference(resolution,[],[f86,f45])).
% 1.53/0.62  fof(f45,plain,(
% 1.53/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f27])).
% 1.53/0.62  fof(f27,plain,(
% 1.53/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.53/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f26])).
% 1.53/0.62  fof(f26,plain,(
% 1.53/0.62    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.53/0.62    introduced(choice_axiom,[])).
% 1.53/0.62  fof(f21,plain,(
% 1.53/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.53/0.62    inference(ennf_transformation,[],[f18])).
% 1.53/0.62  fof(f18,plain,(
% 1.53/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.62    inference(rectify,[],[f5])).
% 1.53/0.62  fof(f5,axiom,(
% 1.53/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.53/0.62  fof(f86,plain,(
% 1.53/0.62    ( ! [X4,X5,X3] : (~r2_hidden(sK3(X3,k4_xboole_0(X4,X5)),X5) | r1_xboole_0(X3,k4_xboole_0(X4,X5))) )),
% 1.53/0.62    inference(resolution,[],[f56,f46])).
% 1.53/0.62  fof(f46,plain,(
% 1.53/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f27])).
% 1.53/0.62  fof(f56,plain,(
% 1.53/0.62    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.53/0.62    inference(equality_resolution,[],[f50])).
% 1.53/0.62  fof(f50,plain,(
% 1.53/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.53/0.62    inference(cnf_transformation,[],[f32])).
% 1.53/0.62  fof(f32,plain,(
% 1.53/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.53/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 1.53/0.62  fof(f31,plain,(
% 1.53/0.62    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.53/0.62    introduced(choice_axiom,[])).
% 1.53/0.62  fof(f30,plain,(
% 1.53/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.53/0.62    inference(rectify,[],[f29])).
% 1.53/0.62  fof(f29,plain,(
% 1.53/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.53/0.62    inference(flattening,[],[f28])).
% 1.53/0.62  fof(f28,plain,(
% 1.53/0.62    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.53/0.62    inference(nnf_transformation,[],[f3])).
% 1.53/0.62  fof(f3,axiom,(
% 1.53/0.62    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.53/0.62  fof(f695,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X2) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.53/0.62    inference(resolution,[],[f147,f43])).
% 1.53/0.62  fof(f43,plain,(
% 1.53/0.62    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f25])).
% 1.53/0.62  fof(f25,plain,(
% 1.53/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.53/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f24])).
% 1.53/0.62  fof(f24,plain,(
% 1.53/0.62    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 1.53/0.62    introduced(choice_axiom,[])).
% 1.53/0.62  fof(f20,plain,(
% 1.53/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.53/0.62    inference(ennf_transformation,[],[f17])).
% 1.53/0.62  fof(f17,plain,(
% 1.53/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.62    inference(rectify,[],[f6])).
% 1.53/0.62  fof(f6,axiom,(
% 1.53/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.53/0.62  fof(f147,plain,(
% 1.53/0.62    ( ! [X12,X10,X13,X11] : (~r2_hidden(X13,k3_xboole_0(X10,k3_xboole_0(X11,X12))) | ~r1_xboole_0(k3_xboole_0(X10,X11),X12)) )),
% 1.53/0.62    inference(superposition,[],[f44,f48])).
% 1.53/0.62  fof(f48,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.53/0.62    inference(cnf_transformation,[],[f7])).
% 1.53/0.62  fof(f7,axiom,(
% 1.53/0.62    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.53/0.62  fof(f44,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f25])).
% 1.53/0.62  fof(f76,plain,(
% 1.53/0.62    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0)) ) | ~spl5_1),
% 1.53/0.62    inference(avatar_component_clause,[],[f75])).
% 1.53/0.62  fof(f75,plain,(
% 1.53/0.62    spl5_1 <=> ! [X0] : ~r1_xboole_0(X0,k1_xboole_0)),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.53/0.62  fof(f3272,plain,(
% 1.53/0.62    ~spl5_2),
% 1.53/0.62    inference(avatar_contradiction_clause,[],[f3271])).
% 1.53/0.62  fof(f3271,plain,(
% 1.53/0.62    $false | ~spl5_2),
% 1.53/0.62    inference(trivial_inequality_removal,[],[f3270])).
% 1.53/0.62  fof(f3270,plain,(
% 1.53/0.62    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1) | ~spl5_2),
% 1.53/0.62    inference(superposition,[],[f33,f2923])).
% 1.53/0.62  fof(f2923,plain,(
% 1.53/0.62    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl5_2),
% 1.53/0.62    inference(backward_demodulation,[],[f340,f2922])).
% 1.53/0.62  fof(f2922,plain,(
% 1.53/0.62    ( ! [X50,X48,X49] : (k3_xboole_0(X50,X48) = k4_xboole_0(k3_xboole_0(X50,X48),k4_xboole_0(X49,X48))) ) | ~spl5_2),
% 1.53/0.62    inference(forward_demodulation,[],[f2921,f36])).
% 1.53/0.62  fof(f36,plain,(
% 1.53/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.53/0.62    inference(cnf_transformation,[],[f11])).
% 1.53/0.62  fof(f11,axiom,(
% 1.53/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.53/0.62  fof(f2921,plain,(
% 1.53/0.62    ( ! [X50,X48,X49] : (k4_xboole_0(k3_xboole_0(X50,X48),k1_xboole_0) = k4_xboole_0(k3_xboole_0(X50,X48),k4_xboole_0(X49,X48))) ) | ~spl5_2),
% 1.53/0.62    inference(forward_demodulation,[],[f2836,f34])).
% 1.53/0.62  fof(f2836,plain,(
% 1.53/0.62    ( ! [X50,X48,X49] : (k4_xboole_0(k3_xboole_0(X50,X48),k3_xboole_0(X50,k1_xboole_0)) = k4_xboole_0(k3_xboole_0(X50,X48),k4_xboole_0(X49,X48))) ) | ~spl5_2),
% 1.53/0.62    inference(superposition,[],[f146,f2323])).
% 1.53/0.62  fof(f2323,plain,(
% 1.53/0.62    ( ! [X10,X11] : (k1_xboole_0 = k3_xboole_0(X10,k4_xboole_0(X11,X10))) ) | ~spl5_2),
% 1.53/0.62    inference(resolution,[],[f1439,f1297])).
% 1.53/0.62  fof(f1297,plain,(
% 1.53/0.62    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.53/0.62    inference(superposition,[],[f1081,f37])).
% 1.53/0.62  fof(f37,plain,(
% 1.53/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.53/0.62    inference(cnf_transformation,[],[f16])).
% 1.53/0.62  fof(f16,plain,(
% 1.53/0.62    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.53/0.62    inference(rectify,[],[f4])).
% 1.53/0.62  fof(f4,axiom,(
% 1.53/0.62    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.53/0.62  fof(f1081,plain,(
% 1.53/0.62    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k1_xboole_0 | ~r1_xboole_0(X1,X2)) )),
% 1.53/0.62    inference(forward_demodulation,[],[f1080,f120])).
% 1.53/0.62  fof(f120,plain,(
% 1.53/0.62    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(X7,X7)) )),
% 1.53/0.62    inference(backward_demodulation,[],[f104,f119])).
% 1.53/0.62  fof(f119,plain,(
% 1.53/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.53/0.62    inference(forward_demodulation,[],[f115,f36])).
% 1.53/0.62  fof(f115,plain,(
% 1.53/0.62    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.53/0.62    inference(superposition,[],[f41,f62])).
% 1.53/0.62  fof(f104,plain,(
% 1.53/0.62    ( ! [X7] : (k4_xboole_0(k1_xboole_0,X7) = k4_xboole_0(X7,X7)) )),
% 1.53/0.62    inference(superposition,[],[f42,f58])).
% 1.53/0.62  fof(f58,plain,(
% 1.53/0.62    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.53/0.62    inference(superposition,[],[f38,f35])).
% 1.53/0.62  fof(f35,plain,(
% 1.53/0.62    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.53/0.62    inference(cnf_transformation,[],[f8])).
% 1.53/0.62  fof(f8,axiom,(
% 1.53/0.62    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.53/0.62  fof(f38,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f1])).
% 1.53/0.62  fof(f1,axiom,(
% 1.53/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.53/0.62  fof(f42,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f12])).
% 1.53/0.62  fof(f12,axiom,(
% 1.53/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.53/0.62  fof(f1080,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k4_xboole_0(X0,X0) | ~r1_xboole_0(X1,X2)) )),
% 1.53/0.62    inference(subsumption_resolution,[],[f1079,f44])).
% 1.53/0.62  fof(f1079,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k4_xboole_0(X0,X0) | ~r1_xboole_0(X1,X2) | r2_hidden(sK4(X0,X0,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X2))) )),
% 1.53/0.62    inference(duplicate_literal_removal,[],[f1057])).
% 1.53/0.62  fof(f1057,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k4_xboole_0(X0,X0) | ~r1_xboole_0(X1,X2) | k3_xboole_0(X1,X2) = k4_xboole_0(X0,X0) | r2_hidden(sK4(X0,X0,k3_xboole_0(X1,X2)),k3_xboole_0(X1,X2))) )),
% 1.53/0.62    inference(resolution,[],[f167,f53])).
% 1.53/0.62  fof(f53,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.53/0.62    inference(cnf_transformation,[],[f32])).
% 1.53/0.62  fof(f167,plain,(
% 1.53/0.62    ( ! [X2,X0,X3,X1] : (r2_hidden(sK4(X0,X1,k3_xboole_0(X2,X3)),X0) | k4_xboole_0(X0,X1) = k3_xboole_0(X2,X3) | ~r1_xboole_0(X2,X3)) )),
% 1.53/0.62    inference(resolution,[],[f52,f44])).
% 1.53/0.62  fof(f52,plain,(
% 1.53/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 1.53/0.62    inference(cnf_transformation,[],[f32])).
% 1.53/0.62  fof(f1439,plain,(
% 1.53/0.62    ( ! [X6,X8,X7] : (r1_xboole_0(k3_xboole_0(X6,k4_xboole_0(X7,X6)),X8)) ) | ~spl5_2),
% 1.53/0.62    inference(resolution,[],[f1412,f45])).
% 1.53/0.62  fof(f1412,plain,(
% 1.53/0.62    ( ! [X24,X23,X25] : (~r2_hidden(X25,k3_xboole_0(X24,k4_xboole_0(X23,X24)))) ) | ~spl5_2),
% 1.53/0.62    inference(forward_demodulation,[],[f1411,f39])).
% 1.53/0.62  fof(f1411,plain,(
% 1.53/0.62    ( ! [X24,X23,X25] : (~r2_hidden(X25,k3_xboole_0(k4_xboole_0(X23,X24),X24))) ) | ~spl5_2),
% 1.53/0.62    inference(subsumption_resolution,[],[f1392,f320])).
% 1.53/0.62  fof(f320,plain,(
% 1.53/0.62    ( ! [X4,X5,X3] : (r2_hidden(X5,X3) | ~r2_hidden(X5,k3_xboole_0(X3,X4))) ) | ~spl5_2),
% 1.53/0.62    inference(subsumption_resolution,[],[f315,f79])).
% 1.53/0.62  fof(f79,plain,(
% 1.53/0.62    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl5_2),
% 1.53/0.62    inference(avatar_component_clause,[],[f78])).
% 1.53/0.62  fof(f78,plain,(
% 1.53/0.62    spl5_2 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 1.53/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.53/0.62  fof(f315,plain,(
% 1.53/0.62    ( ! [X4,X5,X3] : (r2_hidden(X5,k1_xboole_0) | r2_hidden(X5,X3) | ~r2_hidden(X5,k3_xboole_0(X3,X4))) )),
% 1.53/0.62    inference(superposition,[],[f55,f287])).
% 1.53/0.62  fof(f287,plain,(
% 1.53/0.62    ( ! [X24,X23] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X23,X24),X23)) )),
% 1.53/0.62    inference(forward_demodulation,[],[f281,f120])).
% 1.53/0.62  fof(f281,plain,(
% 1.53/0.62    ( ! [X24,X23] : (k4_xboole_0(k3_xboole_0(X23,X24),X23) = k4_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X23,X24))) )),
% 1.53/0.62    inference(superposition,[],[f95,f134])).
% 1.53/0.62  fof(f134,plain,(
% 1.53/0.62    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 1.53/0.62    inference(superposition,[],[f48,f37])).
% 1.53/0.62  fof(f55,plain,(
% 1.53/0.62    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.53/0.62    inference(equality_resolution,[],[f51])).
% 1.53/0.62  fof(f51,plain,(
% 1.53/0.62    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.53/0.62    inference(cnf_transformation,[],[f32])).
% 1.53/0.62  fof(f1392,plain,(
% 1.53/0.62    ( ! [X24,X23,X25] : (~r2_hidden(X25,k4_xboole_0(X23,X24)) | ~r2_hidden(X25,k3_xboole_0(k4_xboole_0(X23,X24),X24))) )),
% 1.53/0.62    inference(superposition,[],[f99,f241])).
% 1.53/0.62  fof(f241,plain,(
% 1.53/0.62    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k4_xboole_0(k4_xboole_0(X6,X5),X5)) )),
% 1.53/0.62    inference(forward_demodulation,[],[f233,f101])).
% 1.53/0.62  fof(f101,plain,(
% 1.53/0.62    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 1.53/0.62    inference(superposition,[],[f42,f38])).
% 1.53/0.62  fof(f233,plain,(
% 1.53/0.62    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(X6,X5),X5) = k4_xboole_0(k2_xboole_0(X5,X6),X5)) )),
% 1.53/0.62    inference(superposition,[],[f101,f40])).
% 1.53/0.62  fof(f40,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.53/0.62    inference(cnf_transformation,[],[f10])).
% 1.53/0.62  fof(f10,axiom,(
% 1.53/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.53/0.62  fof(f99,plain,(
% 1.53/0.62    ( ! [X6,X7,X5] : (~r2_hidden(X7,k4_xboole_0(X5,X6)) | ~r2_hidden(X7,k3_xboole_0(X5,X6))) )),
% 1.53/0.62    inference(superposition,[],[f56,f41])).
% 1.53/0.62  fof(f146,plain,(
% 1.53/0.62    ( ! [X8,X7,X9] : (k4_xboole_0(k3_xboole_0(X7,X8),X9) = k4_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k3_xboole_0(X8,X9)))) )),
% 1.53/0.62    inference(superposition,[],[f41,f48])).
% 1.53/0.62  fof(f340,plain,(
% 1.53/0.62    ( ! [X4,X5] : (k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 1.53/0.62    inference(superposition,[],[f42,f322])).
% 1.53/0.62  fof(f322,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.53/0.62    inference(backward_demodulation,[],[f100,f321])).
% 1.53/0.62  fof(f321,plain,(
% 1.53/0.62    ( ! [X6,X7] : (k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6) )),
% 1.53/0.62    inference(forward_demodulation,[],[f316,f35])).
% 1.53/0.62  fof(f316,plain,(
% 1.53/0.62    ( ! [X6,X7] : (k2_xboole_0(X6,k1_xboole_0) = k2_xboole_0(X6,k3_xboole_0(X6,X7))) )),
% 1.53/0.62    inference(superposition,[],[f40,f287])).
% 1.53/0.62  fof(f100,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.53/0.62    inference(forward_demodulation,[],[f97,f38])).
% 1.53/0.62  fof(f97,plain,(
% 1.53/0.62    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 1.53/0.62    inference(superposition,[],[f40,f41])).
% 1.53/0.62  fof(f33,plain,(
% 1.53/0.62    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.53/0.62    inference(cnf_transformation,[],[f23])).
% 1.53/0.62  fof(f23,plain,(
% 1.53/0.62    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.53/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).
% 1.53/0.62  fof(f22,plain,(
% 1.53/0.62    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.53/0.62    introduced(choice_axiom,[])).
% 1.53/0.62  fof(f19,plain,(
% 1.53/0.62    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.53/0.62    inference(ennf_transformation,[],[f15])).
% 1.53/0.62  fof(f15,negated_conjecture,(
% 1.53/0.62    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.53/0.62    inference(negated_conjecture,[],[f14])).
% 1.53/0.62  fof(f14,conjecture,(
% 1.53/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.53/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.53/0.62  fof(f80,plain,(
% 1.53/0.62    spl5_1 | spl5_2),
% 1.53/0.62    inference(avatar_split_clause,[],[f70,f78,f75])).
% 1.53/0.62  fof(f70,plain,(
% 1.53/0.62    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 1.53/0.62    inference(superposition,[],[f44,f34])).
% 1.53/0.62  % SZS output end Proof for theBenchmark
% 1.53/0.62  % (24001)------------------------------
% 1.53/0.62  % (24001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.62  % (24001)Termination reason: Refutation
% 1.53/0.62  
% 1.53/0.62  % (24001)Memory used [KB]: 13048
% 1.53/0.62  % (24001)Time elapsed: 0.202 s
% 1.53/0.62  % (24001)------------------------------
% 1.53/0.62  % (24001)------------------------------
% 1.53/0.62  % (23998)Success in time 0.256 s
%------------------------------------------------------------------------------
