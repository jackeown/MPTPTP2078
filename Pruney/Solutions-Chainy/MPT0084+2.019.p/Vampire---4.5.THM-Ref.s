%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 243 expanded)
%              Number of leaves         :   23 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  214 ( 476 expanded)
%              Number of equality atoms :   65 ( 195 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f36,f41,f47,f53,f60,f90,f96,f238,f244,f287,f533,f551,f826,f1085,f1147])).

fof(f1147,plain,
    ( spl3_31
    | ~ spl3_93 ),
    inference(avatar_split_clause,[],[f1134,f1082,f282])).

fof(f282,plain,
    ( spl3_31
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f1082,plain,
    ( spl3_93
  <=> k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f1134,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_93 ),
    inference(superposition,[],[f20,f1084])).

fof(f1084,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_93 ),
    inference(avatar_component_clause,[],[f1082])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1085,plain,
    ( spl3_93
    | ~ spl3_24
    | ~ spl3_76 ),
    inference(avatar_split_clause,[],[f1058,f823,f235,f1082])).

fof(f235,plain,
    ( spl3_24
  <=> k3_xboole_0(sK0,sK0) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f823,plain,
    ( spl3_76
  <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK0,k3_xboole_0(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f1058,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_24
    | ~ spl3_76 ),
    inference(superposition,[],[f300,f825])).

fof(f825,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK0,k3_xboole_0(sK2,sK2)))
    | ~ spl3_76 ),
    inference(avatar_component_clause,[],[f823])).

fof(f300,plain,
    ( ! [X0] : k3_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k3_xboole_0(sK0,k3_xboole_0(sK0,k4_xboole_0(sK0,X0)))
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f298,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f298,plain,
    ( ! [X0] : k4_xboole_0(k3_xboole_0(sK0,sK0),X0) = k3_xboole_0(sK0,k4_xboole_0(k3_xboole_0(sK0,sK0),X0))
    | ~ spl3_24 ),
    inference(superposition,[],[f26,f237])).

fof(f237,plain,
    ( k3_xboole_0(sK0,sK0) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK0))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f235])).

fof(f826,plain,
    ( spl3_76
    | ~ spl3_6
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f811,f548,f57,f823])).

fof(f57,plain,
    ( spl3_6
  <=> sK0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f548,plain,
    ( spl3_55
  <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f811,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK0,k3_xboole_0(sK2,sK2)))
    | ~ spl3_6
    | ~ spl3_55 ),
    inference(backward_demodulation,[],[f550,f108])).

fof(f108,plain,
    ( ! [X0] : k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k3_xboole_0(sK2,X0))
    | ~ spl3_6 ),
    inference(superposition,[],[f77,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f77,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k3_xboole_0(sK0,k3_xboole_0(sK2,X0))
    | ~ spl3_6 ),
    inference(superposition,[],[f61,f21])).

fof(f61,plain,
    ( ! [X0] : k3_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_6 ),
    inference(superposition,[],[f26,f59])).

fof(f59,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f550,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,sK2))))
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f548])).

fof(f551,plain,
    ( spl3_55
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f546,f530,f548])).

fof(f530,plain,
    ( spl3_52
  <=> r1_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f546,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,sK2))))
    | ~ spl3_52 ),
    inference(resolution,[],[f532,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f532,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,sK2))))
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f530])).

fof(f533,plain,
    ( spl3_52
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f498,f93,f57,f530])).

fof(f93,plain,
    ( spl3_10
  <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f498,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,sK2))))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(trivial_inequality_removal,[],[f493])).

fof(f493,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,sK2))))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(superposition,[],[f219,f95])).

fof(f95,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK2,sK2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f219,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k3_xboole_0(sK0,X2)
        | r1_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,X2))) )
    | ~ spl3_6 ),
    inference(superposition,[],[f23,f135])).

fof(f135,plain,
    ( ! [X1] : k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,X1))) = k3_xboole_0(sK0,X1)
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f134,f21])).

fof(f134,plain,
    ( ! [X1] : k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,X1))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X1))
    | ~ spl3_6 ),
    inference(superposition,[],[f21,f120])).

fof(f120,plain,
    ( ! [X1] : k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,X1)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f111,f61])).

fof(f111,plain,
    ( ! [X1] : k3_xboole_0(sK0,k4_xboole_0(sK2,X1)) = k4_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,X1)))
    | ~ spl3_6 ),
    inference(superposition,[],[f21,f77])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f287,plain,
    ( spl3_3
    | ~ spl3_31
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f255,f241,f282,f38])).

fof(f38,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f241,plain,
    ( spl3_25
  <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f255,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK0)
    | r1_xboole_0(sK0,sK1)
    | ~ spl3_25 ),
    inference(superposition,[],[f23,f243])).

fof(f243,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f241])).

fof(f244,plain,
    ( spl3_25
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f239,f57,f50,f241])).

fof(f50,plain,
    ( spl3_5
  <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f239,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f231,f20])).

fof(f231,plain,
    ( k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(superposition,[],[f159,f52])).

fof(f52,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f159,plain,
    ( ! [X1] : k3_xboole_0(sK0,X1) = k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X1,sK2)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f147,f21])).

fof(f147,plain,
    ( ! [X1] : k4_xboole_0(sK0,k4_xboole_0(sK0,X1)) = k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X1,sK2)))
    | ~ spl3_6 ),
    inference(superposition,[],[f21,f131])).

fof(f131,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,sK2)))
    | ~ spl3_6 ),
    inference(superposition,[],[f120,f20])).

fof(f238,plain,
    ( spl3_24
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f230,f57,f235])).

fof(f230,plain,
    ( k3_xboole_0(sK0,sK0) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK0))
    | ~ spl3_6 ),
    inference(superposition,[],[f159,f59])).

fof(f96,plain,
    ( spl3_10
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f91,f87,f93])).

fof(f87,plain,
    ( spl3_9
  <=> r1_xboole_0(sK0,k4_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f91,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK2,sK2))
    | ~ spl3_9 ),
    inference(resolution,[],[f89,f22])).

fof(f89,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK2,sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f90,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f85,f57,f44,f87])).

fof(f44,plain,
    ( spl3_4
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f85,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK2,sK2))
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,k4_xboole_0(sK2,sK2))
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(superposition,[],[f80,f46])).

fof(f46,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f80,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k4_xboole_0(sK0,X2)
        | r1_xboole_0(sK0,k4_xboole_0(sK2,X2)) )
    | ~ spl3_6 ),
    inference(superposition,[],[f23,f61])).

fof(f60,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f55,f44,f57])).

fof(f55,plain,
    ( sK0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f54,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f54,plain,
    ( k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f21,f46])).

fof(f53,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f48,f28,f50])).

fof(f28,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f48,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f30,f22])).

fof(f30,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f47,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f42,f33,f44])).

fof(f33,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f42,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f35,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f35,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f41,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f15,f38])).

fof(f15,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f36,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f28])).

fof(f17,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (9326)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.43  % (9326)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f1148,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f31,f36,f41,f47,f53,f60,f90,f96,f238,f244,f287,f533,f551,f826,f1085,f1147])).
% 0.21/0.43  fof(f1147,plain,(
% 0.21/0.43    spl3_31 | ~spl3_93),
% 0.21/0.43    inference(avatar_split_clause,[],[f1134,f1082,f282])).
% 0.21/0.43  fof(f282,plain,(
% 0.21/0.43    spl3_31 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.43  fof(f1082,plain,(
% 0.21/0.43    spl3_93 <=> k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 0.21/0.43  fof(f1134,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) | ~spl3_93),
% 0.21/0.43    inference(superposition,[],[f20,f1084])).
% 0.21/0.43  fof(f1084,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0) | ~spl3_93),
% 0.21/0.43    inference(avatar_component_clause,[],[f1082])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.43  fof(f1085,plain,(
% 0.21/0.43    spl3_93 | ~spl3_24 | ~spl3_76),
% 0.21/0.43    inference(avatar_split_clause,[],[f1058,f823,f235,f1082])).
% 0.21/0.43  fof(f235,plain,(
% 0.21/0.43    spl3_24 <=> k3_xboole_0(sK0,sK0) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.43  fof(f823,plain,(
% 0.21/0.43    spl3_76 <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK0,k3_xboole_0(sK2,sK2)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 0.21/0.43  fof(f1058,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,k1_xboole_0) | (~spl3_24 | ~spl3_76)),
% 0.21/0.43    inference(superposition,[],[f300,f825])).
% 0.21/0.43  fof(f825,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK0,k3_xboole_0(sK2,sK2))) | ~spl3_76),
% 0.21/0.43    inference(avatar_component_clause,[],[f823])).
% 0.21/0.43  fof(f300,plain,(
% 0.21/0.43    ( ! [X0] : (k3_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k3_xboole_0(sK0,k3_xboole_0(sK0,k4_xboole_0(sK0,X0)))) ) | ~spl3_24),
% 0.21/0.43    inference(forward_demodulation,[],[f298,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.43  fof(f298,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(k3_xboole_0(sK0,sK0),X0) = k3_xboole_0(sK0,k4_xboole_0(k3_xboole_0(sK0,sK0),X0))) ) | ~spl3_24),
% 0.21/0.43    inference(superposition,[],[f26,f237])).
% 0.21/0.43  fof(f237,plain,(
% 0.21/0.43    k3_xboole_0(sK0,sK0) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK0)) | ~spl3_24),
% 0.21/0.43    inference(avatar_component_clause,[],[f235])).
% 0.21/0.43  fof(f826,plain,(
% 0.21/0.43    spl3_76 | ~spl3_6 | ~spl3_55),
% 0.21/0.43    inference(avatar_split_clause,[],[f811,f548,f57,f823])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl3_6 <=> sK0 = k3_xboole_0(sK0,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.43  fof(f548,plain,(
% 0.21/0.43    spl3_55 <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,sK2))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.21/0.43  fof(f811,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK0,k3_xboole_0(sK2,sK2))) | (~spl3_6 | ~spl3_55)),
% 0.21/0.43    inference(backward_demodulation,[],[f550,f108])).
% 0.21/0.43  fof(f108,plain,(
% 0.21/0.43    ( ! [X0] : (k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,X0))) = k4_xboole_0(sK0,k3_xboole_0(sK2,X0))) ) | ~spl3_6),
% 0.21/0.43    inference(superposition,[],[f77,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k3_xboole_0(sK0,k3_xboole_0(sK2,X0))) ) | ~spl3_6),
% 0.21/0.43    inference(superposition,[],[f61,f21])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    ( ! [X0] : (k3_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) ) | ~spl3_6),
% 0.21/0.43    inference(superposition,[],[f26,f59])).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    sK0 = k3_xboole_0(sK0,sK2) | ~spl3_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f57])).
% 0.21/0.43  fof(f550,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,sK2)))) | ~spl3_55),
% 0.21/0.43    inference(avatar_component_clause,[],[f548])).
% 0.21/0.43  fof(f551,plain,(
% 0.21/0.43    spl3_55 | ~spl3_52),
% 0.21/0.43    inference(avatar_split_clause,[],[f546,f530,f548])).
% 0.21/0.43  fof(f530,plain,(
% 0.21/0.43    spl3_52 <=> r1_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,sK2))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.21/0.43  fof(f546,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,sK2)))) | ~spl3_52),
% 0.21/0.43    inference(resolution,[],[f532,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(nnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.43  fof(f532,plain,(
% 0.21/0.43    r1_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,sK2)))) | ~spl3_52),
% 0.21/0.43    inference(avatar_component_clause,[],[f530])).
% 0.21/0.43  fof(f533,plain,(
% 0.21/0.43    spl3_52 | ~spl3_6 | ~spl3_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f498,f93,f57,f530])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    spl3_10 <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK2,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.43  fof(f498,plain,(
% 0.21/0.43    r1_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,sK2)))) | (~spl3_6 | ~spl3_10)),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f493])).
% 0.21/0.43  fof(f493,plain,(
% 0.21/0.43    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,k4_xboole_0(sK2,sK2)))) | (~spl3_6 | ~spl3_10)),
% 0.21/0.43    inference(superposition,[],[f219,f95])).
% 0.21/0.43  fof(f95,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK2,sK2)) | ~spl3_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f93])).
% 0.21/0.43  fof(f219,plain,(
% 0.21/0.43    ( ! [X2] : (k1_xboole_0 != k3_xboole_0(sK0,X2) | r1_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,X2)))) ) | ~spl3_6),
% 0.21/0.43    inference(superposition,[],[f23,f135])).
% 0.21/0.43  fof(f135,plain,(
% 0.21/0.43    ( ! [X1] : (k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,X1))) = k3_xboole_0(sK0,X1)) ) | ~spl3_6),
% 0.21/0.43    inference(forward_demodulation,[],[f134,f21])).
% 0.21/0.43  fof(f134,plain,(
% 0.21/0.43    ( ! [X1] : (k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,X1))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X1))) ) | ~spl3_6),
% 0.21/0.43    inference(superposition,[],[f21,f120])).
% 0.21/0.43  fof(f120,plain,(
% 0.21/0.43    ( ! [X1] : (k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,X1)))) ) | ~spl3_6),
% 0.21/0.43    inference(forward_demodulation,[],[f111,f61])).
% 0.21/0.43  fof(f111,plain,(
% 0.21/0.43    ( ! [X1] : (k3_xboole_0(sK0,k4_xboole_0(sK2,X1)) = k4_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(sK2,X1)))) ) | ~spl3_6),
% 0.21/0.43    inference(superposition,[],[f21,f77])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f287,plain,(
% 0.21/0.43    spl3_3 | ~spl3_31 | ~spl3_25),
% 0.21/0.43    inference(avatar_split_clause,[],[f255,f241,f282,f38])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    spl3_3 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f241,plain,(
% 0.21/0.43    spl3_25 <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.43  fof(f255,plain,(
% 0.21/0.43    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK0) | r1_xboole_0(sK0,sK1) | ~spl3_25),
% 0.21/0.43    inference(superposition,[],[f23,f243])).
% 0.21/0.43  fof(f243,plain,(
% 0.21/0.43    k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0) | ~spl3_25),
% 0.21/0.43    inference(avatar_component_clause,[],[f241])).
% 0.21/0.43  fof(f244,plain,(
% 0.21/0.43    spl3_25 | ~spl3_5 | ~spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f239,f57,f50,f241])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    spl3_5 <=> k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.43  fof(f239,plain,(
% 0.21/0.43    k3_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0) | (~spl3_5 | ~spl3_6)),
% 0.21/0.43    inference(forward_demodulation,[],[f231,f20])).
% 0.21/0.43  fof(f231,plain,(
% 0.21/0.43    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0) | (~spl3_5 | ~spl3_6)),
% 0.21/0.43    inference(superposition,[],[f159,f52])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f50])).
% 0.21/0.43  fof(f159,plain,(
% 0.21/0.43    ( ! [X1] : (k3_xboole_0(sK0,X1) = k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X1,sK2)))) ) | ~spl3_6),
% 0.21/0.43    inference(forward_demodulation,[],[f147,f21])).
% 0.21/0.43  fof(f147,plain,(
% 0.21/0.43    ( ! [X1] : (k4_xboole_0(sK0,k4_xboole_0(sK0,X1)) = k3_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X1,sK2)))) ) | ~spl3_6),
% 0.21/0.43    inference(superposition,[],[f21,f131])).
% 0.21/0.43  fof(f131,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,sK2)))) ) | ~spl3_6),
% 0.21/0.43    inference(superposition,[],[f120,f20])).
% 0.21/0.43  fof(f238,plain,(
% 0.21/0.43    spl3_24 | ~spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f230,f57,f235])).
% 0.21/0.43  fof(f230,plain,(
% 0.21/0.43    k3_xboole_0(sK0,sK0) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK0)) | ~spl3_6),
% 0.21/0.43    inference(superposition,[],[f159,f59])).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    spl3_10 | ~spl3_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f91,f87,f93])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    spl3_9 <=> r1_xboole_0(sK0,k4_xboole_0(sK2,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK2,sK2)) | ~spl3_9),
% 0.21/0.43    inference(resolution,[],[f89,f22])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    r1_xboole_0(sK0,k4_xboole_0(sK2,sK2)) | ~spl3_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f87])).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    spl3_9 | ~spl3_4 | ~spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f85,f57,f44,f87])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    spl3_4 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    r1_xboole_0(sK0,k4_xboole_0(sK2,sK2)) | (~spl3_4 | ~spl3_6)),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f82])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,k4_xboole_0(sK2,sK2)) | (~spl3_4 | ~spl3_6)),
% 0.21/0.43    inference(superposition,[],[f80,f46])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl3_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f44])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    ( ! [X2] : (k1_xboole_0 != k4_xboole_0(sK0,X2) | r1_xboole_0(sK0,k4_xboole_0(sK2,X2))) ) | ~spl3_6),
% 0.21/0.43    inference(superposition,[],[f23,f61])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    spl3_6 | ~spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f55,f44,f57])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    sK0 = k3_xboole_0(sK0,sK2) | ~spl3_4),
% 0.21/0.43    inference(forward_demodulation,[],[f54,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_4),
% 0.21/0.43    inference(superposition,[],[f21,f46])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    spl3_5 | ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f48,f28,f50])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    spl3_1 <=> r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.21/0.43    inference(resolution,[],[f30,f22])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f28])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl3_4 | ~spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f42,f33,f44])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    spl3_2 <=> r1_tarski(sK0,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl3_2),
% 0.21/0.43    inference(resolution,[],[f35,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.43    inference(nnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    r1_tarski(sK0,sK2) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f33])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ~spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f15,f38])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.43    inference(negated_conjecture,[],[f8])).
% 0.21/0.43  fof(f8,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f16,f33])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    r1_tarski(sK0,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f17,f28])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (9326)------------------------------
% 0.21/0.43  % (9326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (9326)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (9326)Memory used [KB]: 11385
% 0.21/0.43  % (9326)Time elapsed: 0.025 s
% 0.21/0.43  % (9326)------------------------------
% 0.21/0.43  % (9326)------------------------------
% 0.21/0.44  % (9314)Success in time 0.079 s
%------------------------------------------------------------------------------
