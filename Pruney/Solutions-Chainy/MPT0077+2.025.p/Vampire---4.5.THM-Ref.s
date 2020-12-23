%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 248 expanded)
%              Number of leaves         :   13 (  80 expanded)
%              Depth                    :   16
%              Number of atoms          :  186 ( 486 expanded)
%              Number of equality atoms :   57 ( 204 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f577,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f48,f513,f520,f536,f576])).

fof(f576,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f575])).

fof(f575,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f574])).

fof(f574,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f569,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f24,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f569,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f556,f543])).

fof(f543,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f538,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f538,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(superposition,[],[f31,f537])).

fof(f537,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f46,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f46,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f556,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_1
    | spl3_2 ),
    inference(backward_demodulation,[],[f521,f534])).

fof(f534,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))
    | ~ spl3_1 ),
    inference(superposition,[],[f30,f527])).

fof(f527,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f522,f22])).

fof(f522,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_1 ),
    inference(superposition,[],[f31,f514])).

fof(f514,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1 ),
    inference(resolution,[],[f37,f33])).

fof(f37,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f521,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl3_2 ),
    inference(resolution,[],[f40,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f25])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f536,plain,
    ( spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f21,f39,f45])).

fof(f21,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f520,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f519])).

fof(f519,plain,
    ( $false
    | ~ spl3_2
    | spl3_3 ),
    inference(trivial_inequality_removal,[],[f518])).

fof(f518,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_2
    | spl3_3 ),
    inference(superposition,[],[f517,f43])).

fof(f517,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | ~ spl3_2
    | spl3_3 ),
    inference(forward_demodulation,[],[f516,f407])).

fof(f407,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f394,f361])).

fof(f361,plain,
    ( sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f336,f22])).

fof(f336,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f31,f55])).

fof(f55,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_2 ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f394,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(superposition,[],[f374,f88])).

fof(f88,plain,(
    ! [X4,X5] : k2_xboole_0(X5,X4) = k2_xboole_0(k2_xboole_0(X5,X4),X4) ),
    inference(forward_demodulation,[],[f85,f52])).

fof(f52,plain,(
    ! [X3] : k2_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f50,f23])).

fof(f50,plain,(
    ! [X3] : k2_xboole_0(X3,X3) = k2_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f27,f43])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f85,plain,(
    ! [X4,X5] : k2_xboole_0(k2_xboole_0(X5,X4),X4) = k2_xboole_0(k2_xboole_0(X5,X4),k1_xboole_0) ),
    inference(superposition,[],[f27,f75])).

fof(f75,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,X8)) ),
    inference(forward_demodulation,[],[f67,f27])).

fof(f67,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f30,f43])).

fof(f374,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_2 ),
    inference(superposition,[],[f30,f361])).

fof(f516,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl3_3 ),
    inference(resolution,[],[f47,f32])).

fof(f47,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f513,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f512])).

fof(f512,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f511])).

fof(f511,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_1
    | ~ spl3_2 ),
    inference(superposition,[],[f506,f43])).

fof(f506,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f54,f496])).

fof(f496,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f483,f22])).

fof(f483,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(superposition,[],[f410,f24])).

fof(f410,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f398,f374])).

fof(f398,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))
    | ~ spl3_2 ),
    inference(superposition,[],[f374,f27])).

fof(f54,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl3_1 ),
    inference(resolution,[],[f32,f36])).

fof(f36,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f48,plain,
    ( ~ spl3_2
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f16,f45,f35,f39])).

fof(f16,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f20,f39,f35])).

fof(f20,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (4740)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.44  % (4740)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f577,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f42,f48,f513,f520,f536,f576])).
% 0.20/0.44  fof(f576,plain,(
% 0.20/0.44    ~spl3_1 | spl3_2 | ~spl3_3),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f575])).
% 0.20/0.44  fof(f575,plain,(
% 0.20/0.44    $false | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.20/0.44    inference(trivial_inequality_removal,[],[f574])).
% 0.20/0.44  fof(f574,plain,(
% 0.20/0.44    k1_xboole_0 != k1_xboole_0 | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.20/0.44    inference(superposition,[],[f569,f43])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.44    inference(superposition,[],[f24,f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.44    inference(rectify,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.20/0.44  fof(f569,plain,(
% 0.20/0.44    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.20/0.44    inference(forward_demodulation,[],[f556,f543])).
% 0.20/0.44  fof(f543,plain,(
% 0.20/0.44    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_3),
% 0.20/0.44    inference(forward_demodulation,[],[f538,f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.44  fof(f538,plain,(
% 0.20/0.44    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK2) | ~spl3_3),
% 0.20/0.44    inference(superposition,[],[f31,f537])).
% 0.20/0.44  fof(f537,plain,(
% 0.20/0.44    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_3),
% 0.20/0.44    inference(resolution,[],[f46,f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f28,f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.44    inference(nnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    r1_xboole_0(sK0,sK2) | ~spl3_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f45])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    spl3_3 <=> r1_xboole_0(sK0,sK2)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f26,f25])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.44  fof(f556,plain,(
% 0.20/0.44    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_1 | spl3_2)),
% 0.20/0.44    inference(backward_demodulation,[],[f521,f534])).
% 0.20/0.44  fof(f534,plain,(
% 0.20/0.44    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK1,X0))) ) | ~spl3_1),
% 0.20/0.44    inference(superposition,[],[f30,f527])).
% 0.20/0.44  fof(f527,plain,(
% 0.20/0.44    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_1),
% 0.20/0.44    inference(forward_demodulation,[],[f522,f22])).
% 0.20/0.44  fof(f522,plain,(
% 0.20/0.44    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_1),
% 0.20/0.44    inference(superposition,[],[f31,f514])).
% 0.20/0.44  fof(f514,plain,(
% 0.20/0.44    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_1),
% 0.20/0.44    inference(resolution,[],[f37,f33])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.44  fof(f521,plain,(
% 0.20/0.44    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | spl3_2),
% 0.20/0.44    inference(resolution,[],[f40,f32])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.44    inference(definition_unfolding,[],[f29,f25])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl3_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f39])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    spl3_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.44  fof(f536,plain,(
% 0.20/0.44    spl3_3 | spl3_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f21,f39,f45])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,plain,(
% 0.20/0.44    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.44    inference(ennf_transformation,[],[f10])).
% 0.20/0.44  fof(f10,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.44    inference(negated_conjecture,[],[f9])).
% 0.20/0.44  fof(f9,conjecture,(
% 0.20/0.44    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.20/0.44  fof(f520,plain,(
% 0.20/0.44    ~spl3_2 | spl3_3),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f519])).
% 0.20/0.44  fof(f519,plain,(
% 0.20/0.44    $false | (~spl3_2 | spl3_3)),
% 0.20/0.44    inference(trivial_inequality_removal,[],[f518])).
% 0.20/0.44  fof(f518,plain,(
% 0.20/0.44    k1_xboole_0 != k1_xboole_0 | (~spl3_2 | spl3_3)),
% 0.20/0.44    inference(superposition,[],[f517,f43])).
% 0.20/0.44  fof(f517,plain,(
% 0.20/0.44    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (~spl3_2 | spl3_3)),
% 0.20/0.44    inference(forward_demodulation,[],[f516,f407])).
% 0.20/0.44  fof(f407,plain,(
% 0.20/0.44    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_2),
% 0.20/0.44    inference(forward_demodulation,[],[f394,f361])).
% 0.20/0.44  fof(f361,plain,(
% 0.20/0.44    sK0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.20/0.44    inference(forward_demodulation,[],[f336,f22])).
% 0.20/0.44  fof(f336,plain,(
% 0.20/0.44    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_2),
% 0.20/0.44    inference(superposition,[],[f31,f55])).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | ~spl3_2),
% 0.20/0.44    inference(resolution,[],[f33,f41])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl3_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f39])).
% 0.20/0.44  fof(f394,plain,(
% 0.20/0.44    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,sK2) | ~spl3_2),
% 0.20/0.44    inference(superposition,[],[f374,f88])).
% 0.20/0.44  fof(f88,plain,(
% 0.20/0.44    ( ! [X4,X5] : (k2_xboole_0(X5,X4) = k2_xboole_0(k2_xboole_0(X5,X4),X4)) )),
% 0.20/0.44    inference(forward_demodulation,[],[f85,f52])).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    ( ! [X3] : (k2_xboole_0(X3,k1_xboole_0) = X3) )),
% 0.20/0.44    inference(forward_demodulation,[],[f50,f23])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    ( ! [X3] : (k2_xboole_0(X3,X3) = k2_xboole_0(X3,k1_xboole_0)) )),
% 0.20/0.44    inference(superposition,[],[f27,f43])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.44  fof(f85,plain,(
% 0.20/0.44    ( ! [X4,X5] : (k2_xboole_0(k2_xboole_0(X5,X4),X4) = k2_xboole_0(k2_xboole_0(X5,X4),k1_xboole_0)) )),
% 0.20/0.44    inference(superposition,[],[f27,f75])).
% 0.20/0.44  fof(f75,plain,(
% 0.20/0.44    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,X8))) )),
% 0.20/0.44    inference(forward_demodulation,[],[f67,f27])).
% 0.20/0.44  fof(f67,plain,(
% 0.20/0.44    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9)))) )),
% 0.20/0.44    inference(superposition,[],[f30,f43])).
% 0.20/0.44  fof(f374,plain,(
% 0.20/0.44    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0)) ) | ~spl3_2),
% 0.20/0.44    inference(superposition,[],[f30,f361])).
% 0.20/0.44  fof(f516,plain,(
% 0.20/0.44    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | spl3_3),
% 0.20/0.44    inference(resolution,[],[f47,f32])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    ~r1_xboole_0(sK0,sK2) | spl3_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f45])).
% 0.20/0.44  fof(f513,plain,(
% 0.20/0.44    spl3_1 | ~spl3_2),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f512])).
% 0.20/0.44  fof(f512,plain,(
% 0.20/0.44    $false | (spl3_1 | ~spl3_2)),
% 0.20/0.44    inference(trivial_inequality_removal,[],[f511])).
% 0.20/0.44  fof(f511,plain,(
% 0.20/0.44    k1_xboole_0 != k1_xboole_0 | (spl3_1 | ~spl3_2)),
% 0.20/0.44    inference(superposition,[],[f506,f43])).
% 0.20/0.44  fof(f506,plain,(
% 0.20/0.44    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (spl3_1 | ~spl3_2)),
% 0.20/0.44    inference(backward_demodulation,[],[f54,f496])).
% 0.20/0.44  fof(f496,plain,(
% 0.20/0.44    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_2),
% 0.20/0.44    inference(forward_demodulation,[],[f483,f22])).
% 0.20/0.44  fof(f483,plain,(
% 0.20/0.44    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_2),
% 0.20/0.44    inference(superposition,[],[f410,f24])).
% 0.20/0.44  fof(f410,plain,(
% 0.20/0.44    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) ) | ~spl3_2),
% 0.20/0.44    inference(forward_demodulation,[],[f398,f374])).
% 0.20/0.44  fof(f398,plain,(
% 0.20/0.44    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) ) | ~spl3_2),
% 0.20/0.44    inference(superposition,[],[f374,f27])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl3_1),
% 0.20/0.44    inference(resolution,[],[f32,f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    ~r1_xboole_0(sK0,sK1) | spl3_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f35])).
% 0.20/0.44  fof(f48,plain,(
% 0.20/0.44    ~spl3_2 | ~spl3_1 | ~spl3_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f16,f45,f35,f39])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    spl3_1 | spl3_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f20,f39,f35])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (4740)------------------------------
% 0.20/0.44  % (4740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (4740)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (4740)Memory used [KB]: 6396
% 0.20/0.44  % (4740)Time elapsed: 0.018 s
% 0.20/0.44  % (4740)------------------------------
% 0.20/0.44  % (4740)------------------------------
% 0.20/0.44  % (4735)Success in time 0.087 s
%------------------------------------------------------------------------------
