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
% DateTime   : Thu Dec  3 12:31:34 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 226 expanded)
%              Number of leaves         :   13 (  80 expanded)
%              Depth                    :   18
%              Number of atoms          :  110 ( 279 expanded)
%              Number of equality atoms :   57 ( 201 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2528,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f113,f118,f2433])).

fof(f2433,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f2432])).

fof(f2432,plain,
    ( $false
    | spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f2431,f112])).

fof(f112,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_3
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f2431,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f2430,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f26,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f2430,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK1,sK1)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f2429,f18])).

fof(f2429,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f2295,f31])).

fof(f2295,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)))
    | ~ spl3_4 ),
    inference(superposition,[],[f1724,f131])).

fof(f131,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X0)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f121,f96])).

fof(f96,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f95,f18])).

fof(f95,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f86,f31])).

fof(f86,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f30,f18])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f25,f20])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f121,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f30,f117])).

fof(f117,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_4
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1724,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2))))) ),
    inference(backward_demodulation,[],[f476,f1683])).

fof(f1683,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ),
    inference(superposition,[],[f266,f30])).

fof(f266,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k4_xboole_0(X6,k4_xboole_0(X4,X5))) = k2_xboole_0(k4_xboole_0(X4,X6),k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f30,f72])).

fof(f72,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f60,f18])).

fof(f60,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3) ),
    inference(superposition,[],[f29,f31])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f24,f20,f20])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f476,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))))) ),
    inference(forward_demodulation,[],[f475,f18])).

fof(f475,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),X2))) ),
    inference(forward_demodulation,[],[f393,f31])).

fof(f393,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X0)),X2))) ),
    inference(superposition,[],[f76,f106])).

fof(f106,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    inference(backward_demodulation,[],[f97,f105])).

fof(f105,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3 ),
    inference(forward_demodulation,[],[f104,f18])).

fof(f104,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f90,f31])).

fof(f90,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k4_xboole_0(X4,X4)) ),
    inference(superposition,[],[f30,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f97,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f87,f18])).

fof(f87,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f30,f31])).

fof(f76,plain,(
    ! [X6,X4,X7,X5] : k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6)))),X7))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X6,X7))))))) ),
    inference(forward_demodulation,[],[f75,f29])).

fof(f75,plain,(
    ! [X6,X4,X7,X5] : k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6)))),X7))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X6,X7))))) ),
    inference(forward_demodulation,[],[f74,f29])).

fof(f74,plain,(
    ! [X6,X4,X7,X5] : k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X6,X7))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6)))),X7))) ),
    inference(forward_demodulation,[],[f73,f29])).

fof(f73,plain,(
    ! [X6,X4,X7,X5] : k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X6,X7))) = k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6)))))),X7) ),
    inference(forward_demodulation,[],[f61,f29])).

fof(f61,plain,(
    ! [X6,X4,X7,X5] : k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X6,X7))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6)))),X7) ),
    inference(superposition,[],[f29,f29])).

fof(f118,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f49,f33,f115])).

fof(f33,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f49,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f35,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f35,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f113,plain,
    ( ~ spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f45,f38,f110])).

fof(f38,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f40,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f41,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f16,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f36,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f33])).

fof(f15,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.39  % (14900)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.13/0.40  % (14901)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.42  % (14899)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.42  % (14912)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.43  % (14903)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.43  % (14911)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.43  % (14904)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.43  % (14898)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.43  % (14907)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.43  % (14909)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.44  % (14906)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.44  % (14902)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.44  % (14908)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.44  % (14905)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.45  % (14915)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.45  % (14913)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.45  % (14910)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (14914)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.84/0.62  % (14913)Refutation found. Thanks to Tanya!
% 1.84/0.62  % SZS status Theorem for theBenchmark
% 1.84/0.62  % SZS output start Proof for theBenchmark
% 1.84/0.62  fof(f2528,plain,(
% 1.84/0.62    $false),
% 1.84/0.62    inference(avatar_sat_refutation,[],[f36,f41,f113,f118,f2433])).
% 1.84/0.62  fof(f2433,plain,(
% 1.84/0.62    spl3_3 | ~spl3_4),
% 1.84/0.62    inference(avatar_contradiction_clause,[],[f2432])).
% 1.84/0.62  fof(f2432,plain,(
% 1.84/0.62    $false | (spl3_3 | ~spl3_4)),
% 1.84/0.62    inference(subsumption_resolution,[],[f2431,f112])).
% 1.84/0.62  fof(f112,plain,(
% 1.84/0.62    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) | spl3_3),
% 1.84/0.62    inference(avatar_component_clause,[],[f110])).
% 1.84/0.62  fof(f110,plain,(
% 1.84/0.62    spl3_3 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))),
% 1.84/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.84/0.62  fof(f2431,plain,(
% 1.84/0.62    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) | ~spl3_4),
% 1.84/0.62    inference(forward_demodulation,[],[f2430,f31])).
% 1.84/0.62  fof(f31,plain,(
% 1.84/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.84/0.62    inference(backward_demodulation,[],[f26,f18])).
% 1.84/0.62  fof(f18,plain,(
% 1.84/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.84/0.62    inference(cnf_transformation,[],[f4])).
% 1.84/0.62  fof(f4,axiom,(
% 1.84/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.84/0.62  fof(f26,plain,(
% 1.84/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.84/0.62    inference(definition_unfolding,[],[f17,f20])).
% 1.84/0.62  fof(f20,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.84/0.62    inference(cnf_transformation,[],[f5])).
% 1.84/0.62  fof(f5,axiom,(
% 1.84/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.84/0.62  fof(f17,plain,(
% 1.84/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f2])).
% 1.84/0.62  fof(f2,axiom,(
% 1.84/0.62    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.84/0.62  fof(f2430,plain,(
% 1.84/0.62    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK1,sK1) | ~spl3_4),
% 1.84/0.62    inference(forward_demodulation,[],[f2429,f18])).
% 1.84/0.62  fof(f2429,plain,(
% 1.84/0.62    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)) | ~spl3_4),
% 1.84/0.62    inference(forward_demodulation,[],[f2295,f31])).
% 1.84/0.62  fof(f2295,plain,(
% 1.84/0.62    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK0))) | ~spl3_4),
% 1.84/0.62    inference(superposition,[],[f1724,f131])).
% 1.84/0.62  fof(f131,plain,(
% 1.84/0.62    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X0)) ) | ~spl3_4),
% 1.84/0.62    inference(forward_demodulation,[],[f121,f96])).
% 1.84/0.62  fof(f96,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) )),
% 1.84/0.62    inference(forward_demodulation,[],[f95,f18])).
% 1.84/0.62  fof(f95,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) )),
% 1.84/0.62    inference(forward_demodulation,[],[f86,f31])).
% 1.84/0.62  fof(f86,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0))) )),
% 1.84/0.62    inference(superposition,[],[f30,f18])).
% 1.84/0.62  fof(f30,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 1.84/0.62    inference(definition_unfolding,[],[f25,f20])).
% 1.84/0.62  fof(f25,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.84/0.62    inference(cnf_transformation,[],[f7])).
% 1.84/0.62  fof(f7,axiom,(
% 1.84/0.62    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.84/0.62  fof(f121,plain,(
% 1.84/0.62    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0)) ) | ~spl3_4),
% 1.84/0.62    inference(superposition,[],[f30,f117])).
% 1.84/0.62  fof(f117,plain,(
% 1.84/0.62    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_4),
% 1.84/0.62    inference(avatar_component_clause,[],[f115])).
% 1.84/0.62  fof(f115,plain,(
% 1.84/0.62    spl3_4 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.84/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.84/0.62  fof(f1724,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))))) )),
% 1.84/0.62    inference(backward_demodulation,[],[f476,f1683])).
% 1.84/0.62  fof(f1683,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,X2))))) )),
% 1.84/0.62    inference(superposition,[],[f266,f30])).
% 1.84/0.62  fof(f266,plain,(
% 1.84/0.62    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X6,k4_xboole_0(X4,X5))) = k2_xboole_0(k4_xboole_0(X4,X6),k4_xboole_0(X4,X5))) )),
% 1.84/0.62    inference(superposition,[],[f30,f72])).
% 1.84/0.62  fof(f72,plain,(
% 1.84/0.62    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 1.84/0.62    inference(forward_demodulation,[],[f60,f18])).
% 1.84/0.62  fof(f60,plain,(
% 1.84/0.62    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k4_xboole_0(X2,k1_xboole_0),X3)) )),
% 1.84/0.62    inference(superposition,[],[f29,f31])).
% 1.84/0.62  fof(f29,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.84/0.62    inference(definition_unfolding,[],[f24,f20,f20])).
% 1.84/0.62  fof(f24,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f6])).
% 1.84/0.62  fof(f6,axiom,(
% 1.84/0.62    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.84/0.62  fof(f476,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2)))))))) )),
% 1.84/0.62    inference(forward_demodulation,[],[f475,f18])).
% 1.84/0.62  fof(f475,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k1_xboole_0),X2)))) )),
% 1.84/0.62    inference(forward_demodulation,[],[f393,f31])).
% 1.84/0.62  fof(f393,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X0,X2))))))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X0,X0)),X2)))) )),
% 1.84/0.62    inference(superposition,[],[f76,f106])).
% 1.84/0.62  fof(f106,plain,(
% 1.84/0.62    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) )),
% 1.84/0.62    inference(backward_demodulation,[],[f97,f105])).
% 1.84/0.62  fof(f105,plain,(
% 1.84/0.62    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3) )),
% 1.84/0.62    inference(forward_demodulation,[],[f104,f18])).
% 1.84/0.62  fof(f104,plain,(
% 1.84/0.62    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k1_xboole_0)) )),
% 1.84/0.62    inference(forward_demodulation,[],[f90,f31])).
% 1.84/0.62  fof(f90,plain,(
% 1.84/0.62    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k4_xboole_0(X4,X4))) )),
% 1.84/0.62    inference(superposition,[],[f30,f21])).
% 1.84/0.62  fof(f21,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f3])).
% 1.84/0.62  fof(f3,axiom,(
% 1.84/0.62    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.84/0.62  fof(f97,plain,(
% 1.84/0.62    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 1.84/0.62    inference(forward_demodulation,[],[f87,f18])).
% 1.84/0.62  fof(f87,plain,(
% 1.84/0.62    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0))) )),
% 1.84/0.62    inference(superposition,[],[f30,f31])).
% 1.84/0.62  fof(f76,plain,(
% 1.84/0.62    ( ! [X6,X4,X7,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6)))),X7))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X6,X7)))))))) )),
% 1.84/0.62    inference(forward_demodulation,[],[f75,f29])).
% 1.84/0.62  fof(f75,plain,(
% 1.84/0.62    ( ! [X6,X4,X7,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6)))),X7))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X6,X7)))))) )),
% 1.84/0.62    inference(forward_demodulation,[],[f74,f29])).
% 1.84/0.62  fof(f74,plain,(
% 1.84/0.62    ( ! [X6,X4,X7,X5] : (k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X6,X7))) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6)))),X7)))) )),
% 1.84/0.62    inference(forward_demodulation,[],[f73,f29])).
% 1.84/0.62  fof(f73,plain,(
% 1.84/0.62    ( ! [X6,X4,X7,X5] : (k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X6,X7))) = k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6)))))),X7)) )),
% 1.84/0.62    inference(forward_demodulation,[],[f61,f29])).
% 1.84/0.62  fof(f61,plain,(
% 1.84/0.62    ( ! [X6,X4,X7,X5] : (k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X6,X7))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X5)),k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X5,X6)))),X7)) )),
% 1.84/0.62    inference(superposition,[],[f29,f29])).
% 1.84/0.62  fof(f118,plain,(
% 1.84/0.62    spl3_4 | ~spl3_1),
% 1.84/0.62    inference(avatar_split_clause,[],[f49,f33,f115])).
% 1.84/0.62  fof(f33,plain,(
% 1.84/0.62    spl3_1 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.84/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.84/0.62  fof(f49,plain,(
% 1.84/0.62    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_1),
% 1.84/0.62    inference(unit_resulting_resolution,[],[f35,f28])).
% 1.84/0.62  fof(f28,plain,(
% 1.84/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.84/0.62    inference(definition_unfolding,[],[f22,f20])).
% 1.84/0.62  fof(f22,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f14])).
% 1.84/0.62  fof(f14,plain,(
% 1.84/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.84/0.62    inference(nnf_transformation,[],[f1])).
% 1.84/0.62  fof(f1,axiom,(
% 1.84/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.84/0.62  fof(f35,plain,(
% 1.84/0.62    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 1.84/0.62    inference(avatar_component_clause,[],[f33])).
% 1.84/0.62  fof(f113,plain,(
% 1.84/0.62    ~spl3_3 | spl3_2),
% 1.84/0.62    inference(avatar_split_clause,[],[f45,f38,f110])).
% 1.84/0.62  fof(f38,plain,(
% 1.84/0.62    spl3_2 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.84/0.62    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.84/0.62  fof(f45,plain,(
% 1.84/0.62    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) | spl3_2),
% 1.84/0.62    inference(unit_resulting_resolution,[],[f40,f27])).
% 1.84/0.62  fof(f27,plain,(
% 1.84/0.62    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.84/0.62    inference(definition_unfolding,[],[f23,f20])).
% 1.84/0.62  fof(f23,plain,(
% 1.84/0.62    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.84/0.62    inference(cnf_transformation,[],[f14])).
% 1.84/0.62  fof(f40,plain,(
% 1.84/0.62    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_2),
% 1.84/0.62    inference(avatar_component_clause,[],[f38])).
% 1.84/0.62  fof(f41,plain,(
% 1.84/0.62    ~spl3_2),
% 1.84/0.62    inference(avatar_split_clause,[],[f16,f38])).
% 1.84/0.62  fof(f16,plain,(
% 1.84/0.62    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.84/0.62    inference(cnf_transformation,[],[f13])).
% 1.84/0.62  fof(f13,plain,(
% 1.84/0.62    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.84/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 1.84/0.62  fof(f12,plain,(
% 1.84/0.62    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.84/0.62    introduced(choice_axiom,[])).
% 1.84/0.62  fof(f11,plain,(
% 1.84/0.62    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 1.84/0.62    inference(ennf_transformation,[],[f10])).
% 1.84/0.62  fof(f10,negated_conjecture,(
% 1.84/0.62    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.84/0.62    inference(negated_conjecture,[],[f9])).
% 1.84/0.62  fof(f9,conjecture,(
% 1.84/0.62    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.84/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 1.84/0.62  fof(f36,plain,(
% 1.84/0.62    spl3_1),
% 1.84/0.62    inference(avatar_split_clause,[],[f15,f33])).
% 1.84/0.62  fof(f15,plain,(
% 1.84/0.62    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.84/0.62    inference(cnf_transformation,[],[f13])).
% 1.84/0.62  % SZS output end Proof for theBenchmark
% 1.84/0.62  % (14913)------------------------------
% 1.84/0.62  % (14913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.62  % (14913)Termination reason: Refutation
% 1.84/0.62  
% 1.84/0.62  % (14913)Memory used [KB]: 12409
% 1.84/0.62  % (14913)Time elapsed: 0.233 s
% 1.84/0.62  % (14913)------------------------------
% 1.84/0.62  % (14913)------------------------------
% 2.22/0.64  % (14897)Success in time 0.28 s
%------------------------------------------------------------------------------
