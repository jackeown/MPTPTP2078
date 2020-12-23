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
% DateTime   : Thu Dec  3 12:30:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  148 (1016 expanded)
%              Number of leaves         :   20 ( 322 expanded)
%              Depth                    :   36
%              Number of atoms          :  237 (1767 expanded)
%              Number of equality atoms :  121 (1095 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1355,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f516,f532,f1354])).

fof(f1354,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f1353])).

fof(f1353,plain,
    ( $false
    | ~ spl6_1 ),
    inference(trivial_inequality_removal,[],[f1352])).

fof(f1352,plain,
    ( sK1 != sK1
    | ~ spl6_1 ),
    inference(superposition,[],[f38,f1269])).

fof(f1269,plain,
    ( sK1 = sK2
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f1163,f1212])).

fof(f1212,plain,
    ( sK1 = k4_xboole_0(sK1,sK0)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f420,f1201])).

fof(f1201,plain,
    ( sK0 = sK3
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1200,f39])).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1200,plain,
    ( sK3 = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1195,f1148])).

fof(f1148,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK3)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f539,f1102])).

fof(f1102,plain,(
    ! [X10] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10) ),
    inference(superposition,[],[f489,f111])).

fof(f111,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f90,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f90,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f86,f39])).

fof(f86,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f48,f39])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f489,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5 ),
    inference(backward_demodulation,[],[f367,f488])).

fof(f488,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(forward_demodulation,[],[f465,f396])).

fof(f396,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f57,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f43,f45,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f465,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1 ),
    inference(superposition,[],[f58,f56])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f49,f45])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f367,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5))) = k2_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f354,f44])).

fof(f354,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5))) ),
    inference(superposition,[],[f47,f56])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f539,plain,
    ( k4_xboole_0(sK0,sK3) = k4_xboole_0(k1_xboole_0,sK3)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f535,f121])).

fof(f121,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f48,f111])).

fof(f535,plain,
    ( k4_xboole_0(sK0,sK3) = k4_xboole_0(sK3,sK3)
    | ~ spl6_1 ),
    inference(superposition,[],[f48,f511])).

fof(f511,plain,
    ( sK3 = k2_xboole_0(sK0,sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f509])).

fof(f509,plain,
    ( spl6_1
  <=> sK3 = k2_xboole_0(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1195,plain,
    ( sK3 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK3))
    | ~ spl6_1 ),
    inference(superposition,[],[f57,f1157])).

fof(f1157,plain,
    ( sK3 = k4_xboole_0(sK0,sK1)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1132,f39])).

fof(f1132,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK3,k1_xboole_0)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f977,f1102])).

fof(f977,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f974,f48])).

fof(f974,plain,
    ( k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f358,f965])).

fof(f965,plain,
    ( sK1 = k4_xboole_0(sK2,sK3)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f80,f964])).

fof(f964,plain,
    ( sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f955,f420])).

fof(f955,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3)
    | ~ spl6_1 ),
    inference(superposition,[],[f48,f872])).

fof(f872,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3)
    | ~ spl6_1 ),
    inference(superposition,[],[f564,f271])).

fof(f271,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f53,f144])).

fof(f144,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(forward_demodulation,[],[f143,f111])).

fof(f143,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f142,f44])).

fof(f142,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f141,f47])).

fof(f141,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f47,f129])).

fof(f129,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f89,f128])).

fof(f128,plain,(
    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f81,f121])).

fof(f81,plain,(
    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f48,f71])).

fof(f71,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f52,f61])).

fof(f61,plain,(
    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f42,f35])).

fof(f35,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f89,plain,(
    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f85,f81])).

fof(f85,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f48,f72])).

fof(f72,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f52,f65])).

fof(f65,plain,(
    r1_tarski(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f63,f35])).

fof(f63,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f42,f44])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f564,plain,
    ( ! [X0] : k2_xboole_0(X0,sK3) = k2_xboole_0(sK0,k2_xboole_0(X0,sK3))
    | ~ spl6_1 ),
    inference(superposition,[],[f536,f44])).

fof(f536,plain,
    ( ! [X0] : k2_xboole_0(sK3,X0) = k2_xboole_0(sK0,k2_xboole_0(sK3,X0))
    | ~ spl6_1 ),
    inference(superposition,[],[f53,f511])).

fof(f80,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f48,f35])).

fof(f358,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f346,f129])).

fof(f346,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f56,f80])).

fof(f420,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f399,f39])).

fof(f399,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f57,f231])).

fof(f231,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f227,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f227,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f224,f56])).

fof(f224,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) ),
    inference(resolution,[],[f59,f37])).

fof(f37,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f51,f45])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1163,plain,
    ( sK2 = k4_xboole_0(sK1,sK0)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1135,f39])).

fof(f1135,plain,
    ( k4_xboole_0(sK1,sK0) = k4_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f1030,f1102])).

fof(f1030,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))) = k4_xboole_0(sK1,sK0)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1027,f82])).

fof(f82,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f48,f44])).

fof(f1027,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f361,f1018])).

fof(f1018,plain,
    ( sK0 = k4_xboole_0(sK3,sK2)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f98,f1017])).

fof(f1017,plain,
    ( sK0 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1015,f408])).

fof(f408,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f398,f39])).

fof(f398,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f57,f228])).

fof(f228,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f226,f40])).

fof(f226,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f223,f56])).

fof(f223,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) ),
    inference(resolution,[],[f59,f36])).

fof(f36,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f1015,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl6_1 ),
    inference(backward_demodulation,[],[f338,f1010])).

fof(f1010,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl6_1 ),
    inference(resolution,[],[f1009,f52])).

fof(f1009,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1008,f489])).

fof(f1008,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK2,k4_xboole_0(sK2,sK1)))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1005,f44])).

fof(f1005,plain,
    ( r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK2,sK1),sK2))
    | ~ spl6_1 ),
    inference(superposition,[],[f78,f990])).

fof(f990,plain,
    ( sK1 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | ~ spl6_1 ),
    inference(superposition,[],[f57,f965])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f63,f47])).

fof(f338,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f48,f270])).

fof(f270,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f53,f134])).

fof(f134,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f133,f111])).

fof(f133,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f132,f44])).

fof(f132,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f131,f47])).

fof(f131,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f47,f128])).

fof(f98,plain,(
    k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f48,f95])).

fof(f95,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f94,f72])).

fof(f94,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f93,f47])).

fof(f93,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f47,f80])).

fof(f361,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f347,f128])).

fof(f347,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f56,f98])).

fof(f38,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f532,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f530])).

fof(f530,plain,
    ( $false
    | spl6_2 ),
    inference(resolution,[],[f515,f42])).

fof(f515,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f513])).

fof(f513,plain,
    ( spl6_2
  <=> r1_tarski(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f516,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f500,f513,f509])).

fof(f500,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | sK3 = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f460,f35])).

fof(f460,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,k2_xboole_0(sK2,X0))
      | k2_xboole_0(sK0,X0) = X0 ) ),
    inference(resolution,[],[f449,f52])).

fof(f449,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | ~ r1_tarski(sK0,k2_xboole_0(sK2,X0)) ) ),
    inference(superposition,[],[f54,f408])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n015.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 11:43:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (10985)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.48  % (10993)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.50  % (10977)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (10979)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (11001)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (10975)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (10984)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (10987)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (10997)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (10976)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (10999)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (10992)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (10980)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (10989)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (10978)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (11000)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (11004)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (11003)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (10998)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (10981)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (11002)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (10995)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (10982)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (10996)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (10994)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (10983)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (10990)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (10990)Refutation not found, incomplete strategy% (10990)------------------------------
% 0.21/0.54  % (10990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10990)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10990)Memory used [KB]: 6140
% 0.21/0.54  % (10990)Time elapsed: 0.003 s
% 0.21/0.54  % (10990)------------------------------
% 0.21/0.54  % (10990)------------------------------
% 0.21/0.54  % (10991)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (10988)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (10986)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.58  % (10987)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.60  fof(f1355,plain,(
% 0.21/0.60    $false),
% 0.21/0.60    inference(avatar_sat_refutation,[],[f516,f532,f1354])).
% 0.21/0.60  fof(f1354,plain,(
% 0.21/0.60    ~spl6_1),
% 0.21/0.60    inference(avatar_contradiction_clause,[],[f1353])).
% 0.21/0.60  fof(f1353,plain,(
% 0.21/0.60    $false | ~spl6_1),
% 0.21/0.60    inference(trivial_inequality_removal,[],[f1352])).
% 0.21/0.60  fof(f1352,plain,(
% 0.21/0.60    sK1 != sK1 | ~spl6_1),
% 0.21/0.60    inference(superposition,[],[f38,f1269])).
% 0.21/0.60  fof(f1269,plain,(
% 0.21/0.60    sK1 = sK2 | ~spl6_1),
% 0.21/0.60    inference(backward_demodulation,[],[f1163,f1212])).
% 0.21/0.60  fof(f1212,plain,(
% 0.21/0.60    sK1 = k4_xboole_0(sK1,sK0) | ~spl6_1),
% 0.21/0.60    inference(backward_demodulation,[],[f420,f1201])).
% 0.21/0.60  fof(f1201,plain,(
% 0.21/0.60    sK0 = sK3 | ~spl6_1),
% 0.21/0.60    inference(forward_demodulation,[],[f1200,f39])).
% 0.21/0.60  fof(f39,plain,(
% 0.21/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f8])).
% 0.21/0.60  fof(f8,axiom,(
% 0.21/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.60  fof(f1200,plain,(
% 0.21/0.60    sK3 = k4_xboole_0(sK0,k1_xboole_0) | ~spl6_1),
% 0.21/0.60    inference(forward_demodulation,[],[f1195,f1148])).
% 0.21/0.60  fof(f1148,plain,(
% 0.21/0.60    k1_xboole_0 = k4_xboole_0(sK0,sK3) | ~spl6_1),
% 0.21/0.60    inference(backward_demodulation,[],[f539,f1102])).
% 0.21/0.60  fof(f1102,plain,(
% 0.21/0.60    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10)) )),
% 0.21/0.60    inference(superposition,[],[f489,f111])).
% 0.21/0.60  fof(f111,plain,(
% 0.21/0.60    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.21/0.60    inference(superposition,[],[f90,f44])).
% 0.21/0.60  fof(f44,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f1])).
% 0.21/0.60  fof(f1,axiom,(
% 0.21/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.60  fof(f90,plain,(
% 0.21/0.60    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.21/0.60    inference(forward_demodulation,[],[f86,f39])).
% 0.21/0.60  fof(f86,plain,(
% 0.21/0.60    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 0.21/0.60    inference(superposition,[],[f48,f39])).
% 0.21/0.60  fof(f48,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f9])).
% 0.21/0.60  fof(f9,axiom,(
% 0.21/0.60    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.60  fof(f489,plain,(
% 0.21/0.60    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5) )),
% 0.21/0.60    inference(backward_demodulation,[],[f367,f488])).
% 0.21/0.60  fof(f488,plain,(
% 0.21/0.60    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1) )),
% 0.21/0.60    inference(forward_demodulation,[],[f465,f396])).
% 0.21/0.60  fof(f396,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.21/0.60    inference(superposition,[],[f57,f56])).
% 0.21/0.60  fof(f56,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.60    inference(definition_unfolding,[],[f43,f45,f45])).
% 0.21/0.60  fof(f45,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f12])).
% 0.21/0.60  fof(f12,axiom,(
% 0.21/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.60  fof(f43,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f2])).
% 0.21/0.60  fof(f2,axiom,(
% 0.21/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.60  fof(f57,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.60    inference(definition_unfolding,[],[f46,f45])).
% 0.21/0.60  fof(f46,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f11])).
% 0.21/0.60  fof(f11,axiom,(
% 0.21/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.60  fof(f465,plain,(
% 0.21/0.60    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))),k4_xboole_0(X2,k4_xboole_0(X2,X1))) = X1) )),
% 0.21/0.60    inference(superposition,[],[f58,f56])).
% 0.21/0.60  fof(f58,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.60    inference(definition_unfolding,[],[f49,f45])).
% 0.21/0.60  fof(f49,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f14])).
% 0.21/0.60  fof(f14,axiom,(
% 0.21/0.60    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.60  fof(f367,plain,(
% 0.21/0.60    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5))) = k2_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f354,f44])).
% 0.21/0.60  fof(f354,plain,(
% 0.21/0.60    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5)))) )),
% 0.21/0.60    inference(superposition,[],[f47,f56])).
% 0.21/0.60  fof(f47,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f7])).
% 0.21/0.60  fof(f7,axiom,(
% 0.21/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.60  fof(f539,plain,(
% 0.21/0.60    k4_xboole_0(sK0,sK3) = k4_xboole_0(k1_xboole_0,sK3) | ~spl6_1),
% 0.21/0.60    inference(forward_demodulation,[],[f535,f121])).
% 0.21/0.60  fof(f121,plain,(
% 0.21/0.60    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.60    inference(superposition,[],[f48,f111])).
% 0.21/0.60  fof(f535,plain,(
% 0.21/0.60    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK3,sK3) | ~spl6_1),
% 0.21/0.60    inference(superposition,[],[f48,f511])).
% 0.21/0.60  fof(f511,plain,(
% 0.21/0.60    sK3 = k2_xboole_0(sK0,sK3) | ~spl6_1),
% 0.21/0.60    inference(avatar_component_clause,[],[f509])).
% 0.21/0.60  fof(f509,plain,(
% 0.21/0.60    spl6_1 <=> sK3 = k2_xboole_0(sK0,sK3)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.60  fof(f1195,plain,(
% 0.21/0.60    sK3 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK3)) | ~spl6_1),
% 0.21/0.60    inference(superposition,[],[f57,f1157])).
% 0.21/0.60  fof(f1157,plain,(
% 0.21/0.60    sK3 = k4_xboole_0(sK0,sK1) | ~spl6_1),
% 0.21/0.60    inference(forward_demodulation,[],[f1132,f39])).
% 0.21/0.60  fof(f1132,plain,(
% 0.21/0.60    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK3,k1_xboole_0) | ~spl6_1),
% 0.21/0.60    inference(backward_demodulation,[],[f977,f1102])).
% 0.21/0.60  fof(f977,plain,(
% 0.21/0.60    k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1) | ~spl6_1),
% 0.21/0.60    inference(forward_demodulation,[],[f974,f48])).
% 0.21/0.60  fof(f974,plain,(
% 0.21/0.60    k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) | ~spl6_1),
% 0.21/0.60    inference(backward_demodulation,[],[f358,f965])).
% 0.21/0.60  fof(f965,plain,(
% 0.21/0.60    sK1 = k4_xboole_0(sK2,sK3) | ~spl6_1),
% 0.21/0.60    inference(backward_demodulation,[],[f80,f964])).
% 0.21/0.60  fof(f964,plain,(
% 0.21/0.60    sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) | ~spl6_1),
% 0.21/0.60    inference(forward_demodulation,[],[f955,f420])).
% 0.21/0.60  fof(f955,plain,(
% 0.21/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3) | ~spl6_1),
% 0.21/0.60    inference(superposition,[],[f48,f872])).
% 0.21/0.60  fof(f872,plain,(
% 0.21/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3) | ~spl6_1),
% 0.21/0.60    inference(superposition,[],[f564,f271])).
% 0.21/0.60  fof(f271,plain,(
% 0.21/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))),
% 0.21/0.60    inference(superposition,[],[f53,f144])).
% 0.21/0.60  fof(f144,plain,(
% 0.21/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 0.21/0.60    inference(forward_demodulation,[],[f143,f111])).
% 0.21/0.60  fof(f143,plain,(
% 0.21/0.60    k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(forward_demodulation,[],[f142,f44])).
% 0.21/0.60  fof(f142,plain,(
% 0.21/0.60    k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.21/0.60    inference(forward_demodulation,[],[f141,f47])).
% 0.21/0.60  fof(f141,plain,(
% 0.21/0.60    k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)))),
% 0.21/0.60    inference(superposition,[],[f47,f129])).
% 0.21/0.60  fof(f129,plain,(
% 0.21/0.60    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(backward_demodulation,[],[f89,f128])).
% 0.21/0.60  fof(f128,plain,(
% 0.21/0.60    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(backward_demodulation,[],[f81,f121])).
% 0.21/0.60  fof(f81,plain,(
% 0.21/0.60    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(superposition,[],[f48,f71])).
% 0.21/0.60  fof(f71,plain,(
% 0.21/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(resolution,[],[f52,f61])).
% 0.21/0.60  fof(f61,plain,(
% 0.21/0.60    r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(superposition,[],[f42,f35])).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.21/0.60    inference(cnf_transformation,[],[f30])).
% 0.21/0.60  fof(f30,plain,(
% 0.21/0.60    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f29])).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f22,plain,(
% 0.21/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 0.21/0.60    inference(flattening,[],[f21])).
% 0.21/0.60  fof(f21,plain,(
% 0.21/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 0.21/0.60    inference(ennf_transformation,[],[f18])).
% 0.21/0.60  fof(f18,negated_conjecture,(
% 0.21/0.60    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 0.21/0.60    inference(negated_conjecture,[],[f17])).
% 0.21/0.60  fof(f17,conjecture,(
% 0.21/0.60    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 0.21/0.60  fof(f42,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f16])).
% 0.21/0.60  fof(f16,axiom,(
% 0.21/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.60  fof(f52,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f25])).
% 0.21/0.60  fof(f25,plain,(
% 0.21/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.60    inference(ennf_transformation,[],[f6])).
% 0.21/0.60  fof(f6,axiom,(
% 0.21/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.60  fof(f89,plain,(
% 0.21/0.60    k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(forward_demodulation,[],[f85,f81])).
% 0.21/0.60  fof(f85,plain,(
% 0.21/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(superposition,[],[f48,f72])).
% 0.21/0.60  fof(f72,plain,(
% 0.21/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(resolution,[],[f52,f65])).
% 0.21/0.60  fof(f65,plain,(
% 0.21/0.60    r1_tarski(sK3,k2_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(superposition,[],[f63,f35])).
% 0.21/0.60  fof(f63,plain,(
% 0.21/0.60    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 0.21/0.60    inference(superposition,[],[f42,f44])).
% 0.21/0.60  fof(f53,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f13])).
% 0.21/0.60  fof(f13,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.60  fof(f564,plain,(
% 0.21/0.60    ( ! [X0] : (k2_xboole_0(X0,sK3) = k2_xboole_0(sK0,k2_xboole_0(X0,sK3))) ) | ~spl6_1),
% 0.21/0.60    inference(superposition,[],[f536,f44])).
% 0.21/0.60  fof(f536,plain,(
% 0.21/0.60    ( ! [X0] : (k2_xboole_0(sK3,X0) = k2_xboole_0(sK0,k2_xboole_0(sK3,X0))) ) | ~spl6_1),
% 0.21/0.60    inference(superposition,[],[f53,f511])).
% 0.21/0.60  fof(f80,plain,(
% 0.21/0.60    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 0.21/0.60    inference(superposition,[],[f48,f35])).
% 0.21/0.60  fof(f358,plain,(
% 0.21/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)))),
% 0.21/0.60    inference(forward_demodulation,[],[f346,f129])).
% 0.21/0.60  fof(f346,plain,(
% 0.21/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK2,sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)))),
% 0.21/0.60    inference(superposition,[],[f56,f80])).
% 0.21/0.60  fof(f420,plain,(
% 0.21/0.60    sK1 = k4_xboole_0(sK1,sK3)),
% 0.21/0.60    inference(forward_demodulation,[],[f399,f39])).
% 0.21/0.60  fof(f399,plain,(
% 0.21/0.60    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.60    inference(superposition,[],[f57,f231])).
% 0.21/0.60  fof(f231,plain,(
% 0.21/0.60    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 0.21/0.60    inference(resolution,[],[f227,f40])).
% 0.21/0.60  fof(f40,plain,(
% 0.21/0.60    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f32])).
% 0.21/0.60  fof(f32,plain,(
% 0.21/0.60    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f31])).
% 0.21/0.60  fof(f31,plain,(
% 0.21/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f23,plain,(
% 0.21/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.60    inference(ennf_transformation,[],[f5])).
% 0.21/0.60  fof(f5,axiom,(
% 0.21/0.60    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.60  fof(f227,plain,(
% 0.21/0.60    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f224,f56])).
% 0.21/0.60  fof(f224,plain,(
% 0.21/0.60    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))) )),
% 0.21/0.60    inference(resolution,[],[f59,f37])).
% 0.21/0.60  fof(f37,plain,(
% 0.21/0.60    r1_xboole_0(sK3,sK1)),
% 0.21/0.60    inference(cnf_transformation,[],[f30])).
% 0.21/0.60  fof(f59,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.60    inference(definition_unfolding,[],[f51,f45])).
% 0.21/0.60  fof(f51,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f34])).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f33])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f24,plain,(
% 0.21/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.60    inference(ennf_transformation,[],[f20])).
% 0.21/0.60  fof(f20,plain,(
% 0.21/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.60    inference(rectify,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.60  fof(f1163,plain,(
% 0.21/0.60    sK2 = k4_xboole_0(sK1,sK0) | ~spl6_1),
% 0.21/0.60    inference(forward_demodulation,[],[f1135,f39])).
% 0.21/0.60  fof(f1135,plain,(
% 0.21/0.60    k4_xboole_0(sK1,sK0) = k4_xboole_0(sK2,k1_xboole_0) | ~spl6_1),
% 0.21/0.60    inference(backward_demodulation,[],[f1030,f1102])).
% 0.21/0.60  fof(f1030,plain,(
% 0.21/0.60    k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))) = k4_xboole_0(sK1,sK0) | ~spl6_1),
% 0.21/0.60    inference(forward_demodulation,[],[f1027,f82])).
% 0.21/0.60  fof(f82,plain,(
% 0.21/0.60    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 0.21/0.60    inference(superposition,[],[f48,f44])).
% 0.21/0.60  fof(f1027,plain,(
% 0.21/0.60    k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0) | ~spl6_1),
% 0.21/0.60    inference(backward_demodulation,[],[f361,f1018])).
% 0.21/0.60  fof(f1018,plain,(
% 0.21/0.60    sK0 = k4_xboole_0(sK3,sK2) | ~spl6_1),
% 0.21/0.60    inference(backward_demodulation,[],[f98,f1017])).
% 0.21/0.60  fof(f1017,plain,(
% 0.21/0.60    sK0 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) | ~spl6_1),
% 0.21/0.60    inference(forward_demodulation,[],[f1015,f408])).
% 0.21/0.60  fof(f408,plain,(
% 0.21/0.60    sK0 = k4_xboole_0(sK0,sK2)),
% 0.21/0.60    inference(forward_demodulation,[],[f398,f39])).
% 0.21/0.60  fof(f398,plain,(
% 0.21/0.60    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.60    inference(superposition,[],[f57,f228])).
% 0.21/0.60  fof(f228,plain,(
% 0.21/0.60    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.21/0.60    inference(resolution,[],[f226,f40])).
% 0.21/0.60  fof(f226,plain,(
% 0.21/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f223,f56])).
% 0.21/0.60  fof(f223,plain,(
% 0.21/0.60    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)))) )),
% 0.21/0.60    inference(resolution,[],[f59,f36])).
% 0.21/0.60  fof(f36,plain,(
% 0.21/0.60    r1_xboole_0(sK2,sK0)),
% 0.21/0.60    inference(cnf_transformation,[],[f30])).
% 0.21/0.60  fof(f1015,plain,(
% 0.21/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,sK2) | ~spl6_1),
% 0.21/0.60    inference(backward_demodulation,[],[f338,f1010])).
% 0.21/0.60  fof(f1010,plain,(
% 0.21/0.60    sK2 = k2_xboole_0(sK1,sK2) | ~spl6_1),
% 0.21/0.60    inference(resolution,[],[f1009,f52])).
% 0.21/0.60  fof(f1009,plain,(
% 0.21/0.60    r1_tarski(sK1,sK2) | ~spl6_1),
% 0.21/0.60    inference(forward_demodulation,[],[f1008,f489])).
% 0.21/0.60  fof(f1008,plain,(
% 0.21/0.60    r1_tarski(sK1,k2_xboole_0(sK2,k4_xboole_0(sK2,sK1))) | ~spl6_1),
% 0.21/0.60    inference(forward_demodulation,[],[f1005,f44])).
% 0.21/0.60  fof(f1005,plain,(
% 0.21/0.60    r1_tarski(sK1,k2_xboole_0(k4_xboole_0(sK2,sK1),sK2)) | ~spl6_1),
% 0.21/0.60    inference(superposition,[],[f78,f990])).
% 0.21/0.60  fof(f990,plain,(
% 0.21/0.60    sK1 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) | ~spl6_1),
% 0.21/0.60    inference(superposition,[],[f57,f965])).
% 0.21/0.60  fof(f78,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(superposition,[],[f63,f47])).
% 0.21/0.60  fof(f338,plain,(
% 0.21/0.60    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK2))),
% 0.21/0.60    inference(superposition,[],[f48,f270])).
% 0.21/0.60  fof(f270,plain,(
% 0.21/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.21/0.60    inference(superposition,[],[f53,f134])).
% 0.21/0.60  fof(f134,plain,(
% 0.21/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 0.21/0.60    inference(forward_demodulation,[],[f133,f111])).
% 0.21/0.60  fof(f133,plain,(
% 0.21/0.60    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(forward_demodulation,[],[f132,f44])).
% 0.21/0.60  fof(f132,plain,(
% 0.21/0.60    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.21/0.60    inference(forward_demodulation,[],[f131,f47])).
% 0.21/0.60  fof(f131,plain,(
% 0.21/0.60    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)))),
% 0.21/0.60    inference(superposition,[],[f47,f128])).
% 0.21/0.60  fof(f98,plain,(
% 0.21/0.60    k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 0.21/0.60    inference(superposition,[],[f48,f95])).
% 0.21/0.60  fof(f95,plain,(
% 0.21/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 0.21/0.60    inference(forward_demodulation,[],[f94,f72])).
% 0.21/0.60  fof(f94,plain,(
% 0.21/0.60    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.21/0.60    inference(forward_demodulation,[],[f93,f47])).
% 0.21/0.60  fof(f93,plain,(
% 0.21/0.60    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 0.21/0.60    inference(superposition,[],[f47,f80])).
% 0.21/0.60  fof(f361,plain,(
% 0.21/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)))),
% 0.21/0.60    inference(forward_demodulation,[],[f347,f128])).
% 0.21/0.60  fof(f347,plain,(
% 0.21/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK3,sK2)) = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)))),
% 0.21/0.60    inference(superposition,[],[f56,f98])).
% 0.21/0.60  fof(f38,plain,(
% 0.21/0.60    sK1 != sK2),
% 0.21/0.60    inference(cnf_transformation,[],[f30])).
% 0.21/0.60  fof(f532,plain,(
% 0.21/0.60    spl6_2),
% 0.21/0.60    inference(avatar_contradiction_clause,[],[f530])).
% 0.21/0.60  fof(f530,plain,(
% 0.21/0.60    $false | spl6_2),
% 0.21/0.60    inference(resolution,[],[f515,f42])).
% 0.21/0.60  fof(f515,plain,(
% 0.21/0.60    ~r1_tarski(sK0,k2_xboole_0(sK0,sK1)) | spl6_2),
% 0.21/0.60    inference(avatar_component_clause,[],[f513])).
% 0.21/0.60  fof(f513,plain,(
% 0.21/0.60    spl6_2 <=> r1_tarski(sK0,k2_xboole_0(sK0,sK1))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.60  fof(f516,plain,(
% 0.21/0.60    spl6_1 | ~spl6_2),
% 0.21/0.60    inference(avatar_split_clause,[],[f500,f513,f509])).
% 0.21/0.60  fof(f500,plain,(
% 0.21/0.60    ~r1_tarski(sK0,k2_xboole_0(sK0,sK1)) | sK3 = k2_xboole_0(sK0,sK3)),
% 0.21/0.60    inference(superposition,[],[f460,f35])).
% 0.21/0.60  fof(f460,plain,(
% 0.21/0.60    ( ! [X0] : (~r1_tarski(sK0,k2_xboole_0(sK2,X0)) | k2_xboole_0(sK0,X0) = X0) )),
% 0.21/0.60    inference(resolution,[],[f449,f52])).
% 0.21/0.60  fof(f449,plain,(
% 0.21/0.60    ( ! [X0] : (r1_tarski(sK0,X0) | ~r1_tarski(sK0,k2_xboole_0(sK2,X0))) )),
% 0.21/0.60    inference(superposition,[],[f54,f408])).
% 0.21/0.60  fof(f54,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f26])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.60    inference(ennf_transformation,[],[f10])).
% 0.21/0.60  fof(f10,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.60  % SZS output end Proof for theBenchmark
% 0.21/0.60  % (10987)------------------------------
% 0.21/0.60  % (10987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (10987)Termination reason: Refutation
% 0.21/0.60  
% 0.21/0.60  % (10987)Memory used [KB]: 6908
% 0.21/0.60  % (10987)Time elapsed: 0.176 s
% 0.21/0.60  % (10987)------------------------------
% 0.21/0.60  % (10987)------------------------------
% 0.21/0.60  % (10974)Success in time 0.249 s
%------------------------------------------------------------------------------
