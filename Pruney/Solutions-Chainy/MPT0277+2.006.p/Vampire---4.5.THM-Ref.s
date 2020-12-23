%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:31 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 379 expanded)
%              Number of leaves         :   27 ( 132 expanded)
%              Depth                    :   16
%              Number of atoms          :  392 ( 964 expanded)
%              Number of equality atoms :  216 ( 696 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f553,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f199,f258,f277,f278,f291,f313,f317,f337,f343,f376,f444,f463,f490,f515,f539,f552])).

fof(f552,plain,
    ( spl3_5
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f548])).

fof(f548,plain,
    ( $false
    | spl3_5
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f198,f492])).

fof(f492,plain,
    ( ! [X1] : r1_tarski(sK0,k2_tarski(X1,sK2))
    | ~ spl3_7 ),
    inference(superposition,[],[f80,f253])).

fof(f253,plain,
    ( sK0 = k2_tarski(sK2,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl3_7
  <=> sK0 = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f80,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f198,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl3_5
  <=> r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f539,plain,
    ( ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f530,f251,f139])).

fof(f139,plain,
    ( spl3_3
  <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f530,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))))
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f529])).

fof(f529,plain,
    ( sK0 != sK0
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f260,f253])).

fof(f260,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))))
    | sK0 != k2_tarski(sK2,sK2) ),
    inference(forward_demodulation,[],[f65,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f65,plain,
    ( sK0 != k2_tarski(sK2,sK2)
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k2_tarski(sK1,sK2)),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))) ),
    inference(definition_unfolding,[],[f37,f44,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f49,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f60,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f37,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ( sK0 != k2_tarski(sK1,sK2)
        & sK0 != k1_tarski(sK2)
        & sK0 != k1_tarski(sK1)
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
    & ( sK0 = k2_tarski(sK1,sK2)
      | sK0 = k1_tarski(sK2)
      | sK0 = k1_tarski(sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) )
   => ( ( ( sK0 != k2_tarski(sK1,sK2)
          & sK0 != k1_tarski(sK2)
          & sK0 != k1_tarski(sK1)
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
      & ( sK0 = k2_tarski(sK1,sK2)
        | sK0 = k1_tarski(sK2)
        | sK0 = k1_tarski(sK1)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f515,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f465,f95,f139])).

fof(f95,plain,
    ( spl3_1
  <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k2_tarski(sK1,sK2)),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f465,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f97,f46])).

fof(f97,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k2_tarski(sK1,sK2)),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f490,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f475,f198])).

fof(f475,plain,
    ( ! [X2] : r1_tarski(sK0,k2_tarski(sK1,X2))
    | ~ spl3_6 ),
    inference(superposition,[],[f81,f249])).

fof(f249,plain,
    ( sK0 = k2_tarski(sK1,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl3_6
  <=> sK0 = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f81,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f463,plain,
    ( ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f257,f450])).

fof(f450,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | ~ spl3_9 ),
    inference(trivial_inequality_removal,[],[f449])).

fof(f449,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 != k2_tarski(sK1,sK2)
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f448,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f448,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | sK0 != k2_tarski(sK1,sK2)
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f447,f51])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f447,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0))
    | sK0 != k2_tarski(sK1,sK2)
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f446,f52])).

fof(f446,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK1,sK2))))
    | sK0 != k2_tarski(sK1,sK2)
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f261,f290])).

fof(f290,plain,
    ( k2_tarski(sK1,sK2) = k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl3_9
  <=> k2_tarski(sK1,sK2) = k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f261,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))))
    | sK0 != k2_tarski(sK1,sK2) ),
    inference(forward_demodulation,[],[f64,f46])).

fof(f64,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k2_tarski(sK1,sK2)),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))) ),
    inference(definition_unfolding,[],[f38,f63])).

fof(f38,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f257,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f255])).

fof(f255,plain,
    ( spl3_8
  <=> sK0 = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f444,plain,
    ( spl3_2
    | ~ spl3_5
    | spl3_6
    | spl3_7
    | spl3_8 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | spl3_2
    | ~ spl3_5
    | spl3_6
    | spl3_7
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f101,f256,f248,f197,f252,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0
      | k2_tarski(X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f39,f44,f44])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f252,plain,
    ( sK0 != k2_tarski(sK2,sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f251])).

fof(f197,plain,
    ( r1_tarski(sK0,k2_tarski(sK1,sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f196])).

fof(f248,plain,
    ( sK0 != k2_tarski(sK1,sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f247])).

fof(f256,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f255])).

fof(f101,plain,
    ( k1_xboole_0 != sK0
    | spl3_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f376,plain,
    ( spl3_5
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | spl3_5
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f198,f371])).

fof(f371,plain,
    ( r1_tarski(sK0,k2_tarski(sK1,sK2))
    | ~ spl3_9 ),
    inference(superposition,[],[f77,f290])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f59,f50])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f343,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f339])).

fof(f339,plain,
    ( $false
    | spl3_14 ),
    inference(unit_resulting_resolution,[],[f169,f336,f167])).

fof(f167,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f75,f156])).

fof(f156,plain,(
    ! [X8] : k3_tarski(k2_tarski(X8,k1_xboole_0)) = X8 ),
    inference(forward_demodulation,[],[f147,f51])).

fof(f147,plain,(
    ! [X8] : k5_xboole_0(X8,k1_xboole_0) = k3_tarski(k2_tarski(X8,k1_xboole_0)) ),
    inference(superposition,[],[f134,f112])).

fof(f112,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_tarski(k2_tarski(X0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f74,f51])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k2_tarski(X0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f53,f62])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f134,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f116,f86])).

fof(f86,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f47,f51])).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f116,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f46,f52])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f50])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f336,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl3_14
  <=> r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f169,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f167,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f337,plain,
    ( ~ spl3_14
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_split_clause,[],[f319,f196,f99,f334])).

fof(f319,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2))
    | ~ spl3_2
    | spl3_5 ),
    inference(superposition,[],[f198,f100])).

fof(f100,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f317,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | spl3_11 ),
    inference(unit_resulting_resolution,[],[f83,f312])).

fof(f312,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl3_11
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f313,plain,
    ( ~ spl3_11
    | spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f293,f255,f196,f310])).

fof(f293,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_5
    | ~ spl3_8 ),
    inference(superposition,[],[f198,f257])).

fof(f291,plain,
    ( spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f285,f161,f288])).

fof(f161,plain,
    ( spl3_4
  <=> k1_xboole_0 = k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f285,plain,
    ( k2_tarski(sK1,sK2) = k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f283,f51])).

fof(f283,plain,
    ( k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))) = k5_xboole_0(k2_tarski(sK1,sK2),k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f134,f162])).

fof(f162,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f161])).

fof(f278,plain,
    ( ~ spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f259,f139,f247])).

fof(f259,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))))
    | sK0 != k2_tarski(sK1,sK1) ),
    inference(forward_demodulation,[],[f66,f46])).

fof(f66,plain,
    ( sK0 != k2_tarski(sK1,sK1)
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k2_tarski(sK1,sK2)),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))) ),
    inference(definition_unfolding,[],[f36,f44,f63])).

fof(f36,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f277,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f163,f265])).

fof(f265,plain,
    ( k1_xboole_0 = k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))
    | ~ spl3_3 ),
    inference(superposition,[],[f140,f134])).

fof(f140,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f163,plain,
    ( k1_xboole_0 != k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f161])).

fof(f258,plain,
    ( spl3_2
    | spl3_6
    | spl3_7
    | spl3_8
    | spl3_3 ),
    inference(avatar_split_clause,[],[f202,f139,f255,f251,f247,f99])).

fof(f202,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))))
    | sK0 = k2_tarski(sK1,sK2)
    | sK0 = k2_tarski(sK2,sK2)
    | sK0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f68,f46])).

fof(f68,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | sK0 = k2_tarski(sK2,sK2)
    | sK0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k2_tarski(sK1,sK2)),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))) ),
    inference(definition_unfolding,[],[f34,f44,f44,f63])).

fof(f34,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f199,plain,
    ( ~ spl3_5
    | spl3_3 ),
    inference(avatar_split_clause,[],[f194,f139,f196])).

fof(f194,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | spl3_3 ),
    inference(trivial_inequality_removal,[],[f193])).

fof(f193,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | spl3_3 ),
    inference(forward_demodulation,[],[f185,f52])).

fof(f185,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | spl3_3 ),
    inference(superposition,[],[f141,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k2_tarski(X0,X1)))) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f76,f46])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1))) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f62])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f141,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f102,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f67,f99,f95])).

fof(f67,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k2_tarski(sK1,sK2)),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))) ),
    inference(definition_unfolding,[],[f35,f63])).

fof(f35,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:59:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (15771)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (15764)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (15765)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (15787)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (15767)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (15777)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (15772)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (15776)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (15785)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (15777)Refutation not found, incomplete strategy% (15777)------------------------------
% 0.21/0.52  % (15777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15777)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15777)Memory used [KB]: 1663
% 0.21/0.52  % (15777)Time elapsed: 0.071 s
% 0.21/0.52  % (15777)------------------------------
% 0.21/0.52  % (15777)------------------------------
% 0.21/0.52  % (15774)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (15773)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (15779)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (15769)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (15791)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (15783)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (15792)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (15780)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (15792)Refutation not found, incomplete strategy% (15792)------------------------------
% 0.21/0.53  % (15792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15792)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15792)Memory used [KB]: 1663
% 0.21/0.53  % (15792)Time elapsed: 0.123 s
% 0.21/0.53  % (15792)------------------------------
% 0.21/0.53  % (15792)------------------------------
% 0.21/0.53  % (15763)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (15791)Refutation not found, incomplete strategy% (15791)------------------------------
% 0.21/0.53  % (15791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15775)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (15791)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15791)Memory used [KB]: 10746
% 0.21/0.53  % (15791)Time elapsed: 0.090 s
% 0.21/0.53  % (15791)------------------------------
% 0.21/0.53  % (15791)------------------------------
% 0.21/0.54  % (15784)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (15782)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (15781)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (15768)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (15766)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (15786)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (15788)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (15779)Refutation not found, incomplete strategy% (15779)------------------------------
% 0.21/0.54  % (15779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15779)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15779)Memory used [KB]: 10618
% 0.21/0.54  % (15779)Time elapsed: 0.133 s
% 0.21/0.54  % (15779)------------------------------
% 0.21/0.54  % (15779)------------------------------
% 0.21/0.55  % (15773)Refutation not found, incomplete strategy% (15773)------------------------------
% 0.21/0.55  % (15773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15773)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15773)Memory used [KB]: 10746
% 0.21/0.55  % (15773)Time elapsed: 0.118 s
% 0.21/0.55  % (15773)------------------------------
% 0.21/0.55  % (15773)------------------------------
% 0.21/0.55  % (15778)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (15790)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (15789)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (15781)Refutation not found, incomplete strategy% (15781)------------------------------
% 0.21/0.55  % (15781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15781)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15781)Memory used [KB]: 1663
% 0.21/0.55  % (15781)Time elapsed: 0.142 s
% 0.21/0.55  % (15781)------------------------------
% 0.21/0.55  % (15781)------------------------------
% 0.21/0.55  % (15789)Refutation not found, incomplete strategy% (15789)------------------------------
% 0.21/0.55  % (15789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15789)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15789)Memory used [KB]: 6268
% 0.21/0.55  % (15789)Time elapsed: 0.141 s
% 0.21/0.55  % (15789)------------------------------
% 0.21/0.55  % (15789)------------------------------
% 0.21/0.56  % (15770)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (15790)Refutation not found, incomplete strategy% (15790)------------------------------
% 0.21/0.56  % (15790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15790)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15790)Memory used [KB]: 6396
% 0.21/0.56  % (15790)Time elapsed: 0.146 s
% 0.21/0.56  % (15790)------------------------------
% 0.21/0.56  % (15790)------------------------------
% 1.60/0.57  % (15786)Refutation found. Thanks to Tanya!
% 1.60/0.57  % SZS status Theorem for theBenchmark
% 1.60/0.57  % SZS output start Proof for theBenchmark
% 1.60/0.57  fof(f553,plain,(
% 1.60/0.57    $false),
% 1.60/0.57    inference(avatar_sat_refutation,[],[f102,f199,f258,f277,f278,f291,f313,f317,f337,f343,f376,f444,f463,f490,f515,f539,f552])).
% 1.60/0.57  fof(f552,plain,(
% 1.60/0.57    spl3_5 | ~spl3_7),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f548])).
% 1.60/0.57  fof(f548,plain,(
% 1.60/0.57    $false | (spl3_5 | ~spl3_7)),
% 1.60/0.57    inference(subsumption_resolution,[],[f198,f492])).
% 1.60/0.57  fof(f492,plain,(
% 1.60/0.57    ( ! [X1] : (r1_tarski(sK0,k2_tarski(X1,sK2))) ) | ~spl3_7),
% 1.60/0.57    inference(superposition,[],[f80,f253])).
% 1.60/0.57  fof(f253,plain,(
% 1.60/0.57    sK0 = k2_tarski(sK2,sK2) | ~spl3_7),
% 1.60/0.57    inference(avatar_component_clause,[],[f251])).
% 1.60/0.57  fof(f251,plain,(
% 1.60/0.57    spl3_7 <=> sK0 = k2_tarski(sK2,sK2)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.60/0.57  fof(f80,plain,(
% 1.60/0.57    ( ! [X2,X1] : (r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2))) )),
% 1.60/0.57    inference(equality_resolution,[],[f69])).
% 1.60/0.57  fof(f69,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X2,X2) != X0) )),
% 1.60/0.57    inference(definition_unfolding,[],[f42,f44])).
% 1.60/0.57  fof(f44,plain,(
% 1.60/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f14])).
% 1.60/0.57  fof(f14,axiom,(
% 1.60/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.60/0.57  fof(f42,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 1.60/0.57    inference(cnf_transformation,[],[f31])).
% 1.60/0.57  fof(f31,plain,(
% 1.60/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.60/0.57    inference(flattening,[],[f30])).
% 1.60/0.57  fof(f30,plain,(
% 1.60/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.60/0.57    inference(nnf_transformation,[],[f23])).
% 1.60/0.57  fof(f23,plain,(
% 1.60/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.60/0.57    inference(ennf_transformation,[],[f16])).
% 1.60/0.57  fof(f16,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.60/0.57  fof(f198,plain,(
% 1.60/0.57    ~r1_tarski(sK0,k2_tarski(sK1,sK2)) | spl3_5),
% 1.60/0.57    inference(avatar_component_clause,[],[f196])).
% 1.60/0.57  fof(f196,plain,(
% 1.60/0.57    spl3_5 <=> r1_tarski(sK0,k2_tarski(sK1,sK2))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.60/0.57  fof(f539,plain,(
% 1.60/0.57    ~spl3_3 | ~spl3_7),
% 1.60/0.57    inference(avatar_split_clause,[],[f530,f251,f139])).
% 1.60/0.57  fof(f139,plain,(
% 1.60/0.57    spl3_3 <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.60/0.57  fof(f530,plain,(
% 1.60/0.57    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))) | ~spl3_7),
% 1.60/0.57    inference(trivial_inequality_removal,[],[f529])).
% 1.60/0.57  fof(f529,plain,(
% 1.60/0.57    sK0 != sK0 | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))) | ~spl3_7),
% 1.60/0.57    inference(forward_demodulation,[],[f260,f253])).
% 1.60/0.57  fof(f260,plain,(
% 1.60/0.57    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))) | sK0 != k2_tarski(sK2,sK2)),
% 1.60/0.57    inference(forward_demodulation,[],[f65,f46])).
% 1.60/0.57  fof(f46,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f10])).
% 1.60/0.57  fof(f10,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.60/0.57  fof(f65,plain,(
% 1.60/0.57    sK0 != k2_tarski(sK2,sK2) | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k2_tarski(sK1,sK2)),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))),
% 1.60/0.57    inference(definition_unfolding,[],[f37,f44,f63])).
% 1.60/0.57  fof(f63,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1))))) )),
% 1.60/0.57    inference(definition_unfolding,[],[f49,f62])).
% 1.60/0.57  fof(f62,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1)))) )),
% 1.60/0.57    inference(definition_unfolding,[],[f60,f50])).
% 1.60/0.57  fof(f50,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f17])).
% 1.60/0.57  fof(f17,axiom,(
% 1.60/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.60/0.57  fof(f60,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f13])).
% 1.60/0.57  fof(f13,axiom,(
% 1.60/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.60/0.57  fof(f49,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f4])).
% 1.60/0.57  fof(f4,axiom,(
% 1.60/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.60/0.57  fof(f37,plain,(
% 1.60/0.57    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.60/0.57    inference(cnf_transformation,[],[f29])).
% 1.60/0.57  fof(f29,plain,(
% 1.60/0.57    ((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)))),
% 1.60/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).
% 1.60/0.57  fof(f28,plain,(
% 1.60/0.57    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)))) => (((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))))),
% 1.60/0.57    introduced(choice_axiom,[])).
% 1.60/0.57  fof(f27,plain,(
% 1.60/0.57    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 1.60/0.57    inference(flattening,[],[f26])).
% 1.60/0.57  fof(f26,plain,(
% 1.60/0.57    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 1.60/0.57    inference(nnf_transformation,[],[f22])).
% 1.60/0.57  fof(f22,plain,(
% 1.60/0.57    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.60/0.57    inference(ennf_transformation,[],[f20])).
% 1.60/0.57  fof(f20,negated_conjecture,(
% 1.60/0.57    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.60/0.57    inference(negated_conjecture,[],[f19])).
% 1.60/0.57  fof(f19,conjecture,(
% 1.60/0.57    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 1.60/0.57  fof(f515,plain,(
% 1.60/0.57    ~spl3_3 | spl3_1),
% 1.60/0.57    inference(avatar_split_clause,[],[f465,f95,f139])).
% 1.60/0.57  fof(f95,plain,(
% 1.60/0.57    spl3_1 <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k2_tarski(sK1,sK2)),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.60/0.57  fof(f465,plain,(
% 1.60/0.57    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))) | spl3_1),
% 1.60/0.57    inference(forward_demodulation,[],[f97,f46])).
% 1.60/0.57  fof(f97,plain,(
% 1.60/0.57    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k2_tarski(sK1,sK2)),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))) | spl3_1),
% 1.60/0.57    inference(avatar_component_clause,[],[f95])).
% 1.60/0.57  fof(f490,plain,(
% 1.60/0.57    spl3_5 | ~spl3_6),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f487])).
% 1.60/0.57  fof(f487,plain,(
% 1.60/0.57    $false | (spl3_5 | ~spl3_6)),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f475,f198])).
% 1.60/0.57  fof(f475,plain,(
% 1.60/0.57    ( ! [X2] : (r1_tarski(sK0,k2_tarski(sK1,X2))) ) | ~spl3_6),
% 1.60/0.57    inference(superposition,[],[f81,f249])).
% 1.60/0.57  fof(f249,plain,(
% 1.60/0.57    sK0 = k2_tarski(sK1,sK1) | ~spl3_6),
% 1.60/0.57    inference(avatar_component_clause,[],[f247])).
% 1.60/0.57  fof(f247,plain,(
% 1.60/0.57    spl3_6 <=> sK0 = k2_tarski(sK1,sK1)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.60/0.57  fof(f81,plain,(
% 1.60/0.57    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2))) )),
% 1.60/0.57    inference(equality_resolution,[],[f70])).
% 1.60/0.57  fof(f70,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X1) != X0) )),
% 1.60/0.57    inference(definition_unfolding,[],[f41,f44])).
% 1.60/0.57  fof(f41,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 1.60/0.57    inference(cnf_transformation,[],[f31])).
% 1.60/0.57  fof(f463,plain,(
% 1.60/0.57    ~spl3_8 | ~spl3_9),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f461])).
% 1.60/0.57  fof(f461,plain,(
% 1.60/0.57    $false | (~spl3_8 | ~spl3_9)),
% 1.60/0.57    inference(subsumption_resolution,[],[f257,f450])).
% 1.60/0.57  fof(f450,plain,(
% 1.60/0.57    sK0 != k2_tarski(sK1,sK2) | ~spl3_9),
% 1.60/0.57    inference(trivial_inequality_removal,[],[f449])).
% 1.60/0.57  fof(f449,plain,(
% 1.60/0.57    k1_xboole_0 != k1_xboole_0 | sK0 != k2_tarski(sK1,sK2) | ~spl3_9),
% 1.60/0.57    inference(forward_demodulation,[],[f448,f52])).
% 1.60/0.57  fof(f52,plain,(
% 1.60/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f11])).
% 1.60/0.57  fof(f11,axiom,(
% 1.60/0.57    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.60/0.57  fof(f448,plain,(
% 1.60/0.57    k1_xboole_0 != k5_xboole_0(sK0,sK0) | sK0 != k2_tarski(sK1,sK2) | ~spl3_9),
% 1.60/0.57    inference(forward_demodulation,[],[f447,f51])).
% 1.60/0.57  fof(f51,plain,(
% 1.60/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.60/0.57    inference(cnf_transformation,[],[f8])).
% 1.60/0.57  fof(f8,axiom,(
% 1.60/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.60/0.57  fof(f447,plain,(
% 1.60/0.57    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)) | sK0 != k2_tarski(sK1,sK2) | ~spl3_9),
% 1.60/0.57    inference(forward_demodulation,[],[f446,f52])).
% 1.60/0.57  fof(f446,plain,(
% 1.60/0.57    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK1,sK2)))) | sK0 != k2_tarski(sK1,sK2) | ~spl3_9),
% 1.60/0.57    inference(forward_demodulation,[],[f261,f290])).
% 1.60/0.57  fof(f290,plain,(
% 1.60/0.57    k2_tarski(sK1,sK2) = k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))) | ~spl3_9),
% 1.60/0.57    inference(avatar_component_clause,[],[f288])).
% 1.60/0.57  fof(f288,plain,(
% 1.60/0.57    spl3_9 <=> k2_tarski(sK1,sK2) = k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.60/0.57  fof(f261,plain,(
% 1.60/0.57    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))) | sK0 != k2_tarski(sK1,sK2)),
% 1.60/0.57    inference(forward_demodulation,[],[f64,f46])).
% 1.60/0.57  fof(f64,plain,(
% 1.60/0.57    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k2_tarski(sK1,sK2)),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))),
% 1.60/0.57    inference(definition_unfolding,[],[f38,f63])).
% 1.60/0.57  fof(f38,plain,(
% 1.60/0.57    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.60/0.57    inference(cnf_transformation,[],[f29])).
% 1.60/0.57  fof(f257,plain,(
% 1.60/0.57    sK0 = k2_tarski(sK1,sK2) | ~spl3_8),
% 1.60/0.57    inference(avatar_component_clause,[],[f255])).
% 1.60/0.57  fof(f255,plain,(
% 1.60/0.57    spl3_8 <=> sK0 = k2_tarski(sK1,sK2)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.60/0.57  fof(f444,plain,(
% 1.60/0.57    spl3_2 | ~spl3_5 | spl3_6 | spl3_7 | spl3_8),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f438])).
% 1.60/0.57  fof(f438,plain,(
% 1.60/0.57    $false | (spl3_2 | ~spl3_5 | spl3_6 | spl3_7 | spl3_8)),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f101,f256,f248,f197,f252,f71])).
% 1.60/0.57  fof(f71,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0 | k2_tarski(X1,X2) = X0) )),
% 1.60/0.57    inference(definition_unfolding,[],[f39,f44,f44])).
% 1.60/0.57  fof(f39,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f31])).
% 1.60/0.57  fof(f252,plain,(
% 1.60/0.57    sK0 != k2_tarski(sK2,sK2) | spl3_7),
% 1.60/0.57    inference(avatar_component_clause,[],[f251])).
% 1.60/0.57  fof(f197,plain,(
% 1.60/0.57    r1_tarski(sK0,k2_tarski(sK1,sK2)) | ~spl3_5),
% 1.60/0.57    inference(avatar_component_clause,[],[f196])).
% 1.60/0.57  fof(f248,plain,(
% 1.60/0.57    sK0 != k2_tarski(sK1,sK1) | spl3_6),
% 1.60/0.57    inference(avatar_component_clause,[],[f247])).
% 1.60/0.57  fof(f256,plain,(
% 1.60/0.57    sK0 != k2_tarski(sK1,sK2) | spl3_8),
% 1.60/0.57    inference(avatar_component_clause,[],[f255])).
% 1.60/0.57  fof(f101,plain,(
% 1.60/0.57    k1_xboole_0 != sK0 | spl3_2),
% 1.60/0.57    inference(avatar_component_clause,[],[f99])).
% 1.60/0.57  fof(f99,plain,(
% 1.60/0.57    spl3_2 <=> k1_xboole_0 = sK0),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.60/0.57  fof(f376,plain,(
% 1.60/0.57    spl3_5 | ~spl3_9),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f374])).
% 1.60/0.57  fof(f374,plain,(
% 1.60/0.57    $false | (spl3_5 | ~spl3_9)),
% 1.60/0.57    inference(subsumption_resolution,[],[f198,f371])).
% 1.60/0.57  fof(f371,plain,(
% 1.60/0.57    r1_tarski(sK0,k2_tarski(sK1,sK2)) | ~spl3_9),
% 1.60/0.57    inference(superposition,[],[f77,f290])).
% 1.60/0.57  fof(f77,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 1.60/0.57    inference(definition_unfolding,[],[f59,f50])).
% 1.60/0.57  fof(f59,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f9])).
% 1.60/0.57  fof(f9,axiom,(
% 1.60/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.60/0.57  fof(f343,plain,(
% 1.60/0.57    spl3_14),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f339])).
% 1.60/0.57  fof(f339,plain,(
% 1.60/0.57    $false | spl3_14),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f169,f336,f167])).
% 1.60/0.57  fof(f167,plain,(
% 1.60/0.57    ( ! [X2,X1] : (~r1_tarski(X2,k1_xboole_0) | r1_tarski(X2,X1)) )),
% 1.60/0.57    inference(superposition,[],[f75,f156])).
% 1.60/0.57  fof(f156,plain,(
% 1.60/0.57    ( ! [X8] : (k3_tarski(k2_tarski(X8,k1_xboole_0)) = X8) )),
% 1.60/0.57    inference(forward_demodulation,[],[f147,f51])).
% 1.60/0.57  fof(f147,plain,(
% 1.60/0.57    ( ! [X8] : (k5_xboole_0(X8,k1_xboole_0) = k3_tarski(k2_tarski(X8,k1_xboole_0))) )),
% 1.60/0.57    inference(superposition,[],[f134,f112])).
% 1.60/0.57  fof(f112,plain,(
% 1.60/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_tarski(k2_tarski(X0,k1_xboole_0)))) )),
% 1.60/0.57    inference(forward_demodulation,[],[f74,f51])).
% 1.60/0.57  fof(f74,plain,(
% 1.60/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k2_tarski(X0,k1_xboole_0)))) )),
% 1.60/0.57    inference(definition_unfolding,[],[f53,f62])).
% 1.60/0.57  fof(f53,plain,(
% 1.60/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f7])).
% 1.60/0.57  fof(f7,axiom,(
% 1.60/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.60/0.57  fof(f134,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.60/0.57    inference(forward_demodulation,[],[f116,f86])).
% 1.60/0.57  fof(f86,plain,(
% 1.60/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.60/0.57    inference(superposition,[],[f47,f51])).
% 1.60/0.57  fof(f47,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f1])).
% 1.60/0.57  fof(f1,axiom,(
% 1.60/0.57    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.60/0.57  fof(f116,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.60/0.57    inference(superposition,[],[f46,f52])).
% 1.60/0.57  fof(f75,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 1.60/0.57    inference(definition_unfolding,[],[f54,f50])).
% 1.60/0.57  fof(f54,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f24])).
% 1.60/0.57  fof(f24,plain,(
% 1.60/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.60/0.57    inference(ennf_transformation,[],[f5])).
% 1.60/0.57  fof(f5,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.60/0.57  fof(f336,plain,(
% 1.60/0.57    ~r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2)) | spl3_14),
% 1.60/0.57    inference(avatar_component_clause,[],[f334])).
% 1.60/0.57  fof(f334,plain,(
% 1.60/0.57    spl3_14 <=> r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.60/0.57  fof(f169,plain,(
% 1.60/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.60/0.57    inference(resolution,[],[f167,f83])).
% 1.60/0.57  fof(f83,plain,(
% 1.60/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.60/0.57    inference(equality_resolution,[],[f56])).
% 1.60/0.57  fof(f56,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.60/0.57    inference(cnf_transformation,[],[f33])).
% 1.60/0.57  fof(f33,plain,(
% 1.60/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.57    inference(flattening,[],[f32])).
% 1.60/0.57  fof(f32,plain,(
% 1.60/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.60/0.57    inference(nnf_transformation,[],[f3])).
% 1.60/0.57  fof(f3,axiom,(
% 1.60/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.60/0.57  fof(f337,plain,(
% 1.60/0.57    ~spl3_14 | ~spl3_2 | spl3_5),
% 1.60/0.57    inference(avatar_split_clause,[],[f319,f196,f99,f334])).
% 1.60/0.57  fof(f319,plain,(
% 1.60/0.57    ~r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2)) | (~spl3_2 | spl3_5)),
% 1.60/0.57    inference(superposition,[],[f198,f100])).
% 1.60/0.57  fof(f100,plain,(
% 1.60/0.57    k1_xboole_0 = sK0 | ~spl3_2),
% 1.60/0.57    inference(avatar_component_clause,[],[f99])).
% 1.60/0.57  fof(f317,plain,(
% 1.60/0.57    spl3_11),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f314])).
% 1.60/0.57  fof(f314,plain,(
% 1.60/0.57    $false | spl3_11),
% 1.60/0.57    inference(unit_resulting_resolution,[],[f83,f312])).
% 1.60/0.57  fof(f312,plain,(
% 1.60/0.57    ~r1_tarski(sK0,sK0) | spl3_11),
% 1.60/0.57    inference(avatar_component_clause,[],[f310])).
% 1.60/0.57  fof(f310,plain,(
% 1.60/0.57    spl3_11 <=> r1_tarski(sK0,sK0)),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.60/0.57  fof(f313,plain,(
% 1.60/0.57    ~spl3_11 | spl3_5 | ~spl3_8),
% 1.60/0.57    inference(avatar_split_clause,[],[f293,f255,f196,f310])).
% 1.60/0.57  fof(f293,plain,(
% 1.60/0.57    ~r1_tarski(sK0,sK0) | (spl3_5 | ~spl3_8)),
% 1.60/0.57    inference(superposition,[],[f198,f257])).
% 1.60/0.57  fof(f291,plain,(
% 1.60/0.57    spl3_9 | ~spl3_4),
% 1.60/0.57    inference(avatar_split_clause,[],[f285,f161,f288])).
% 1.60/0.57  fof(f161,plain,(
% 1.60/0.57    spl3_4 <=> k1_xboole_0 = k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))))),
% 1.60/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.60/0.57  fof(f285,plain,(
% 1.60/0.57    k2_tarski(sK1,sK2) = k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))) | ~spl3_4),
% 1.60/0.57    inference(forward_demodulation,[],[f283,f51])).
% 1.60/0.57  fof(f283,plain,(
% 1.60/0.57    k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2))) = k5_xboole_0(k2_tarski(sK1,sK2),k1_xboole_0) | ~spl3_4),
% 1.60/0.57    inference(superposition,[],[f134,f162])).
% 1.60/0.57  fof(f162,plain,(
% 1.60/0.57    k1_xboole_0 = k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))) | ~spl3_4),
% 1.60/0.57    inference(avatar_component_clause,[],[f161])).
% 1.60/0.57  fof(f278,plain,(
% 1.60/0.57    ~spl3_6 | ~spl3_3),
% 1.60/0.57    inference(avatar_split_clause,[],[f259,f139,f247])).
% 1.60/0.57  fof(f259,plain,(
% 1.60/0.57    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))) | sK0 != k2_tarski(sK1,sK1)),
% 1.60/0.57    inference(forward_demodulation,[],[f66,f46])).
% 1.60/0.57  fof(f66,plain,(
% 1.60/0.57    sK0 != k2_tarski(sK1,sK1) | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k2_tarski(sK1,sK2)),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))),
% 1.60/0.57    inference(definition_unfolding,[],[f36,f44,f63])).
% 1.60/0.57  fof(f36,plain,(
% 1.60/0.57    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.60/0.57    inference(cnf_transformation,[],[f29])).
% 1.60/0.57  fof(f277,plain,(
% 1.60/0.57    ~spl3_3 | spl3_4),
% 1.60/0.57    inference(avatar_contradiction_clause,[],[f275])).
% 1.60/0.57  fof(f275,plain,(
% 1.60/0.57    $false | (~spl3_3 | spl3_4)),
% 1.60/0.57    inference(subsumption_resolution,[],[f163,f265])).
% 1.60/0.57  fof(f265,plain,(
% 1.60/0.57    k1_xboole_0 = k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))) | ~spl3_3),
% 1.60/0.57    inference(superposition,[],[f140,f134])).
% 1.60/0.57  fof(f140,plain,(
% 1.60/0.57    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))) | ~spl3_3),
% 1.60/0.57    inference(avatar_component_clause,[],[f139])).
% 1.60/0.57  fof(f163,plain,(
% 1.60/0.57    k1_xboole_0 != k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))) | spl3_4),
% 1.60/0.57    inference(avatar_component_clause,[],[f161])).
% 1.60/0.57  fof(f258,plain,(
% 1.60/0.57    spl3_2 | spl3_6 | spl3_7 | spl3_8 | spl3_3),
% 1.60/0.57    inference(avatar_split_clause,[],[f202,f139,f255,f251,f247,f99])).
% 1.60/0.57  fof(f202,plain,(
% 1.60/0.57    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))) | sK0 = k2_tarski(sK1,sK2) | sK0 = k2_tarski(sK2,sK2) | sK0 = k2_tarski(sK1,sK1) | k1_xboole_0 = sK0),
% 1.60/0.57    inference(forward_demodulation,[],[f68,f46])).
% 1.60/0.57  fof(f68,plain,(
% 1.60/0.57    sK0 = k2_tarski(sK1,sK2) | sK0 = k2_tarski(sK2,sK2) | sK0 = k2_tarski(sK1,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k2_tarski(sK1,sK2)),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))),
% 1.60/0.57    inference(definition_unfolding,[],[f34,f44,f44,f63])).
% 1.60/0.57  fof(f34,plain,(
% 1.60/0.57    sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.60/0.57    inference(cnf_transformation,[],[f29])).
% 1.60/0.57  fof(f199,plain,(
% 1.60/0.57    ~spl3_5 | spl3_3),
% 1.60/0.57    inference(avatar_split_clause,[],[f194,f139,f196])).
% 1.60/0.57  fof(f194,plain,(
% 1.60/0.57    ~r1_tarski(sK0,k2_tarski(sK1,sK2)) | spl3_3),
% 1.60/0.57    inference(trivial_inequality_removal,[],[f193])).
% 1.60/0.57  fof(f193,plain,(
% 1.60/0.57    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(sK0,k2_tarski(sK1,sK2)) | spl3_3),
% 1.60/0.57    inference(forward_demodulation,[],[f185,f52])).
% 1.60/0.57  fof(f185,plain,(
% 1.60/0.57    k1_xboole_0 != k5_xboole_0(sK0,sK0) | ~r1_tarski(sK0,k2_tarski(sK1,sK2)) | spl3_3),
% 1.60/0.57    inference(superposition,[],[f141,f165])).
% 1.60/0.57  fof(f165,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k2_tarski(X0,X1)))) = X0 | ~r1_tarski(X0,X1)) )),
% 1.60/0.57    inference(forward_demodulation,[],[f76,f46])).
% 1.60/0.57  fof(f76,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k2_tarski(X0,X1))) = X0 | ~r1_tarski(X0,X1)) )),
% 1.60/0.57    inference(definition_unfolding,[],[f58,f62])).
% 1.60/0.57  fof(f58,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f25])).
% 1.60/0.57  fof(f25,plain,(
% 1.60/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.60/0.57    inference(ennf_transformation,[],[f6])).
% 1.60/0.57  fof(f6,axiom,(
% 1.60/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.60/0.57  fof(f141,plain,(
% 1.60/0.57    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k2_tarski(sK1,sK2),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))) | spl3_3),
% 1.60/0.57    inference(avatar_component_clause,[],[f139])).
% 1.60/0.57  fof(f102,plain,(
% 1.60/0.57    ~spl3_1 | ~spl3_2),
% 1.60/0.57    inference(avatar_split_clause,[],[f67,f99,f95])).
% 1.60/0.57  fof(f67,plain,(
% 1.60/0.57    k1_xboole_0 != sK0 | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k2_tarski(sK1,sK2)),k3_tarski(k2_tarski(sK0,k2_tarski(sK1,sK2)))))),
% 1.60/0.57    inference(definition_unfolding,[],[f35,f63])).
% 1.60/0.57  fof(f35,plain,(
% 1.60/0.57    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 1.60/0.57    inference(cnf_transformation,[],[f29])).
% 1.60/0.57  % SZS output end Proof for theBenchmark
% 1.60/0.57  % (15786)------------------------------
% 1.60/0.57  % (15786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (15786)Termination reason: Refutation
% 1.60/0.57  
% 1.60/0.57  % (15786)Memory used [KB]: 11001
% 1.60/0.57  % (15786)Time elapsed: 0.164 s
% 1.60/0.57  % (15786)------------------------------
% 1.60/0.57  % (15786)------------------------------
% 1.60/0.57  % (15762)Success in time 0.206 s
%------------------------------------------------------------------------------
