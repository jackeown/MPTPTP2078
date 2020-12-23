%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 509 expanded)
%              Number of leaves         :   17 ( 156 expanded)
%              Depth                    :   23
%              Number of atoms          :  214 (1069 expanded)
%              Number of equality atoms :   32 ( 165 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f867,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f91,f125,f131,f281,f864])).

fof(f864,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f855])).

fof(f855,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f39,f74,f828,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f828,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f827,f365])).

fof(f365,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f352,f49])).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f352,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))
    | ~ spl6_2 ),
    inference(superposition,[],[f337,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f48,f47,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f337,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f96,f96,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f96,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f95,f49])).

fof(f95,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f92,f49])).

fof(f92,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f81,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f47])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f81,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f39,f74,f29])).

fof(f827,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f812,f761])).

fof(f761,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl6_2 ),
    inference(superposition,[],[f513,f424])).

fof(f424,plain,
    ( ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl6_2 ),
    inference(superposition,[],[f420,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f420,plain,
    ( ! [X6] : k2_xboole_0(X6,k1_xboole_0) = X6
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f414,f49])).

fof(f414,plain,
    ( ! [X6] : k2_xboole_0(k4_xboole_0(X6,k1_xboole_0),k1_xboole_0) = X6
    | ~ spl6_2 ),
    inference(superposition,[],[f52,f365])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f35,f47])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f513,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))
    | ~ spl6_2 ),
    inference(superposition,[],[f52,f384])).

fof(f384,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f283,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f283,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f64,f51])).

fof(f64,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f812,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(backward_demodulation,[],[f531,f805])).

fof(f805,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(superposition,[],[f33,f795])).

fof(f795,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(superposition,[],[f539,f424])).

fof(f539,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl6_3 ),
    inference(superposition,[],[f52,f452])).

fof(f452,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f286,f46])).

fof(f286,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f90,f51])).

fof(f90,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f531,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))))
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f303,f419])).

fof(f419,plain,
    ( ! [X4,X5] :
        ( ~ r1_xboole_0(X4,X4)
        | ~ r2_hidden(X5,X4) )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f413,f49])).

fof(f413,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,k4_xboole_0(X4,k1_xboole_0))
        | ~ r1_xboole_0(X4,X4) )
    | ~ spl6_2 ),
    inference(superposition,[],[f51,f365])).

fof(f303,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f59,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl6_1
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f74,plain,
    ( r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f68,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f68,plain,
    ( r1_xboole_0(k1_xboole_0,sK2)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f39,f64,f29])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f281,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f60,f203,f30])).

fof(f203,plain,
    ( ! [X1] : ~ r1_xboole_0(k2_xboole_0(X1,sK2),sK0)
    | spl6_2 ),
    inference(superposition,[],[f138,f37])).

fof(f138,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_xboole_0(sK2,X0),sK0)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f38,f133,f29])).

fof(f133,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl6_2 ),
    inference(unit_resulting_resolution,[],[f63,f30])).

fof(f63,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f60,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f131,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl6_1
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f118,f89,f30])).

fof(f89,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f118,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f38,f114,f29])).

fof(f114,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f60,f30])).

fof(f125,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f26,f58,f88,f62])).

fof(f26,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f91,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f28,f88,f58])).

fof(f28,plain,
    ( r1_xboole_0(sK0,sK1)
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f27,f62,f58])).

fof(f27,plain,
    ( r1_xboole_0(sK0,sK2)
    | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:26:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (28635)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.47  % (28635)Refutation not found, incomplete strategy% (28635)------------------------------
% 0.22/0.47  % (28635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (28635)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (28635)Memory used [KB]: 10746
% 0.22/0.47  % (28635)Time elapsed: 0.053 s
% 0.22/0.47  % (28635)------------------------------
% 0.22/0.47  % (28635)------------------------------
% 0.22/0.47  % (28643)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.51  % (28649)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (28632)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (28631)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (28630)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (28641)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (28629)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (28628)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (28629)Refutation not found, incomplete strategy% (28629)------------------------------
% 0.22/0.52  % (28629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28629)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28629)Memory used [KB]: 10746
% 0.22/0.52  % (28629)Time elapsed: 0.116 s
% 0.22/0.52  % (28629)------------------------------
% 0.22/0.52  % (28629)------------------------------
% 0.22/0.52  % (28647)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (28634)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (28645)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (28639)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (28627)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (28633)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (28655)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (28644)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (28644)Refutation not found, incomplete strategy% (28644)------------------------------
% 0.22/0.54  % (28644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28644)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28644)Memory used [KB]: 10618
% 0.22/0.54  % (28644)Time elapsed: 0.129 s
% 0.22/0.54  % (28644)------------------------------
% 0.22/0.54  % (28644)------------------------------
% 0.22/0.54  % (28654)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (28649)Refutation not found, incomplete strategy% (28649)------------------------------
% 0.22/0.54  % (28649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28649)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28649)Memory used [KB]: 10618
% 0.22/0.54  % (28649)Time elapsed: 0.103 s
% 0.22/0.54  % (28649)------------------------------
% 0.22/0.54  % (28649)------------------------------
% 0.22/0.54  % (28636)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (28650)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (28656)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (28637)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (28637)Refutation not found, incomplete strategy% (28637)------------------------------
% 0.22/0.54  % (28637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28637)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28637)Memory used [KB]: 10618
% 0.22/0.54  % (28637)Time elapsed: 0.138 s
% 0.22/0.54  % (28637)------------------------------
% 0.22/0.54  % (28637)------------------------------
% 0.22/0.54  % (28651)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (28631)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f867,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f65,f91,f125,f131,f281,f864])).
% 0.22/0.54  fof(f864,plain,(
% 0.22/0.54    spl6_1 | ~spl6_2 | ~spl6_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f855])).
% 0.22/0.54  fof(f855,plain,(
% 0.22/0.54    $false | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f39,f74,f828,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.54  fof(f828,plain,(
% 0.22/0.54    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.22/0.54    inference(forward_demodulation,[],[f827,f365])).
% 0.22/0.54  fof(f365,plain,(
% 0.22/0.54    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) ) | ~spl6_2),
% 0.22/0.54    inference(forward_demodulation,[],[f352,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.54  fof(f352,plain,(
% 0.22/0.54    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ) | ~spl6_2),
% 0.22/0.54    inference(superposition,[],[f337,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f48,f47,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.54  fof(f337,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl6_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f96,f96,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_2),
% 0.22/0.54    inference(forward_demodulation,[],[f95,f49])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,k1_xboole_0))) ) | ~spl6_2),
% 0.22/0.54    inference(forward_demodulation,[],[f92,f49])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)))) ) | ~spl6_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f81,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f31,f47])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(rectify,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl6_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f39,f74,f29])).
% 0.22/0.55  fof(f827,plain,(
% 0.22/0.55    ~r1_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.22/0.55    inference(forward_demodulation,[],[f812,f761])).
% 0.22/0.55  fof(f761,plain,(
% 0.22/0.55    sK0 = k4_xboole_0(sK0,sK2) | ~spl6_2),
% 0.22/0.55    inference(superposition,[],[f513,f424])).
% 0.22/0.55  fof(f424,plain,(
% 0.22/0.55    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) ) | ~spl6_2),
% 0.22/0.55    inference(superposition,[],[f420,f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.55  fof(f420,plain,(
% 0.22/0.55    ( ! [X6] : (k2_xboole_0(X6,k1_xboole_0) = X6) ) | ~spl6_2),
% 0.22/0.55    inference(forward_demodulation,[],[f414,f49])).
% 0.22/0.55  fof(f414,plain,(
% 0.22/0.55    ( ! [X6] : (k2_xboole_0(k4_xboole_0(X6,k1_xboole_0),k1_xboole_0) = X6) ) | ~spl6_2),
% 0.22/0.55    inference(superposition,[],[f52,f365])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.55    inference(definition_unfolding,[],[f35,f47])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.55  fof(f513,plain,(
% 0.22/0.55    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) | ~spl6_2),
% 0.22/0.55    inference(superposition,[],[f52,f384])).
% 0.22/0.55  fof(f384,plain,(
% 0.22/0.55    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl6_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f283,f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.55  fof(f283,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) ) | ~spl6_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f64,f51])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    r1_xboole_0(sK0,sK2) | ~spl6_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f62])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    spl6_2 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.55  fof(f812,plain,(
% 0.22/0.55    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | (spl6_1 | ~spl6_2 | ~spl6_3)),
% 0.22/0.55    inference(backward_demodulation,[],[f531,f805])).
% 0.22/0.55  fof(f805,plain,(
% 0.22/0.55    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))) ) | (~spl6_2 | ~spl6_3)),
% 0.22/0.55    inference(superposition,[],[f33,f795])).
% 0.22/0.55  fof(f795,plain,(
% 0.22/0.55    sK0 = k4_xboole_0(sK0,sK1) | (~spl6_2 | ~spl6_3)),
% 0.22/0.55    inference(superposition,[],[f539,f424])).
% 0.22/0.55  fof(f539,plain,(
% 0.22/0.55    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) | ~spl6_3),
% 0.22/0.55    inference(superposition,[],[f52,f452])).
% 0.22/0.55  fof(f452,plain,(
% 0.22/0.55    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl6_3),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f286,f46])).
% 0.22/0.55  fof(f286,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ) | ~spl6_3),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f90,f51])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    r1_xboole_0(sK0,sK1) | ~spl6_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f88])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    spl6_3 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.55  fof(f531,plain,(
% 0.22/0.55    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))) | (spl6_1 | ~spl6_2)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f303,f419])).
% 0.22/0.55  fof(f419,plain,(
% 0.22/0.55    ( ! [X4,X5] : (~r1_xboole_0(X4,X4) | ~r2_hidden(X5,X4)) ) | ~spl6_2),
% 0.22/0.55    inference(forward_demodulation,[],[f413,f49])).
% 0.22/0.55  fof(f413,plain,(
% 0.22/0.55    ( ! [X4,X5] : (~r2_hidden(X5,k4_xboole_0(X4,k1_xboole_0)) | ~r1_xboole_0(X4,X4)) ) | ~spl6_2),
% 0.22/0.55    inference(superposition,[],[f51,f365])).
% 0.22/0.55  fof(f303,plain,(
% 0.22/0.55    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))) | spl6_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f59,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f32,f47])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl6_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f58])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    spl6_1 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    r1_xboole_0(sK2,k1_xboole_0) | ~spl6_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f68,f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    r1_xboole_0(k1_xboole_0,sK2) | ~spl6_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f39,f64,f29])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.55  fof(f281,plain,(
% 0.22/0.55    ~spl6_1 | spl6_2),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f270])).
% 0.22/0.55  fof(f270,plain,(
% 0.22/0.55    $false | (~spl6_1 | spl6_2)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f60,f203,f30])).
% 0.22/0.55  fof(f203,plain,(
% 0.22/0.55    ( ! [X1] : (~r1_xboole_0(k2_xboole_0(X1,sK2),sK0)) ) | spl6_2),
% 0.22/0.55    inference(superposition,[],[f138,f37])).
% 0.22/0.55  fof(f138,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(sK2,X0),sK0)) ) | spl6_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f38,f133,f29])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    ~r1_xboole_0(sK2,sK0) | spl6_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f63,f30])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ~r1_xboole_0(sK0,sK2) | spl6_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f62])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl6_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f58])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    ~spl6_1 | spl6_3),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f128])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    $false | (~spl6_1 | spl6_3)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f118,f89,f30])).
% 0.22/0.55  fof(f89,plain,(
% 0.22/0.55    ~r1_xboole_0(sK0,sK1) | spl6_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f88])).
% 0.22/0.55  fof(f118,plain,(
% 0.22/0.55    r1_xboole_0(sK1,sK0) | ~spl6_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f38,f114,f29])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) | ~spl6_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f60,f30])).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    ~spl6_2 | ~spl6_3 | ~spl6_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f26,f58,f88,f62])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.55    inference(ennf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.55    inference(negated_conjecture,[],[f16])).
% 0.22/0.55  fof(f16,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    spl6_1 | spl6_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f28,f88,f58])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    r1_xboole_0(sK0,sK1) | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    spl6_1 | spl6_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f27,f62,f58])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    r1_xboole_0(sK0,sK2) | r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (28631)------------------------------
% 0.22/0.55  % (28631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (28631)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (28631)Memory used [KB]: 6652
% 0.22/0.55  % (28631)Time elapsed: 0.142 s
% 0.22/0.55  % (28631)------------------------------
% 0.22/0.55  % (28631)------------------------------
% 0.22/0.55  % (28626)Success in time 0.187 s
%------------------------------------------------------------------------------
