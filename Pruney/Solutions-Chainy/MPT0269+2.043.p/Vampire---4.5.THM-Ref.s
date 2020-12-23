%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:52 EST 2020

% Result     : Theorem 2.17s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 188 expanded)
%              Number of leaves         :   20 (  69 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 248 expanded)
%              Number of equality atoms :   71 ( 194 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f996,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f163,f278,f993,f995])).

fof(f995,plain,
    ( spl2_2
    | spl2_1
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f994,f990,f59,f64])).

fof(f64,plain,
    ( spl2_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

% (19877)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f59,plain,
    ( spl2_1
  <=> sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f990,plain,
    ( spl2_14
  <=> r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f994,plain,
    ( sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | ~ spl2_14 ),
    inference(resolution,[],[f992,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X1))
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f34,f47,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f992,plain,
    ( r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f990])).

fof(f993,plain,
    ( spl2_14
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f986,f275,f990])).

fof(f275,plain,
    ( spl2_9
  <=> k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f986,plain,
    ( r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ spl2_9 ),
    inference(superposition,[],[f52,f277])).

fof(f277,plain,
    ( k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f275])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f29,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f43])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f278,plain,
    ( spl2_9
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f273,f160,f275])).

fof(f160,plain,
    ( spl2_4
  <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f273,plain,
    ( k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f272,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f272,plain,
    ( k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f258,f96])).

fof(f96,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f74,f90])).

fof(f90,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f83,f25])).

fof(f83,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f74,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f38,f24])).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f258,plain,
    ( k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)))
    | ~ spl2_4 ),
    inference(superposition,[],[f226,f24])).

fof(f226,plain,
    ( ! [X0] : k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),X0)))) = X0
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f225,f90])).

fof(f225,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),X0))))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f224,f38])).

fof(f224,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))),X0)))
    | ~ spl2_4 ),
    inference(forward_demodulation,[],[f199,f38])).

fof(f199,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))))),X0))
    | ~ spl2_4 ),
    inference(superposition,[],[f38,f162])).

fof(f162,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))))))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f160])).

fof(f163,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f158,f69,f160])).

fof(f69,plain,
    ( spl2_3
  <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f158,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))))))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f71,f38])).

fof(f71,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f72,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f49,f69])).

fof(f49,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))))) ),
    inference(definition_unfolding,[],[f21,f46,f47])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f32,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f33,f44])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f21,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f67,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f22,f64])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f48,f59])).

fof(f48,plain,(
    sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f23,f47])).

fof(f23,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:57:42 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (19872)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (19872)Refutation not found, incomplete strategy% (19872)------------------------------
% 0.22/0.54  % (19872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (19885)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (19872)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (19872)Memory used [KB]: 10746
% 0.22/0.55  % (19872)Time elapsed: 0.106 s
% 0.22/0.55  % (19872)------------------------------
% 0.22/0.55  % (19872)------------------------------
% 0.22/0.55  % (19885)Refutation not found, incomplete strategy% (19885)------------------------------
% 0.22/0.55  % (19885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (19885)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (19885)Memory used [KB]: 10746
% 0.22/0.55  % (19885)Time elapsed: 0.113 s
% 0.22/0.55  % (19885)------------------------------
% 0.22/0.55  % (19885)------------------------------
% 1.55/0.57  % (19881)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.55/0.57  % (19863)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.55/0.58  % (19863)Refutation not found, incomplete strategy% (19863)------------------------------
% 1.55/0.58  % (19863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (19863)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (19863)Memory used [KB]: 1791
% 1.55/0.58  % (19863)Time elapsed: 0.137 s
% 1.55/0.58  % (19863)------------------------------
% 1.55/0.58  % (19863)------------------------------
% 1.55/0.58  % (19874)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.55/0.58  % (19874)Refutation not found, incomplete strategy% (19874)------------------------------
% 1.55/0.58  % (19874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (19874)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (19874)Memory used [KB]: 10618
% 1.55/0.58  % (19874)Time elapsed: 0.145 s
% 1.55/0.58  % (19874)------------------------------
% 1.55/0.58  % (19874)------------------------------
% 1.55/0.58  % (19864)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.55/0.58  % (19889)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.55/0.59  % (19868)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.75/0.59  % (19889)Refutation not found, incomplete strategy% (19889)------------------------------
% 1.75/0.59  % (19889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.59  % (19889)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.59  
% 1.75/0.59  % (19889)Memory used [KB]: 10746
% 1.75/0.59  % (19889)Time elapsed: 0.152 s
% 1.75/0.59  % (19889)------------------------------
% 1.75/0.59  % (19889)------------------------------
% 1.75/0.60  % (19879)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.75/0.60  % (19867)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.75/0.60  % (19865)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.75/0.60  % (19865)Refutation not found, incomplete strategy% (19865)------------------------------
% 1.75/0.60  % (19865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.60  % (19865)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.60  
% 1.75/0.60  % (19865)Memory used [KB]: 10746
% 1.75/0.60  % (19865)Time elapsed: 0.168 s
% 1.75/0.60  % (19865)------------------------------
% 1.75/0.60  % (19865)------------------------------
% 1.75/0.60  % (19867)Refutation not found, incomplete strategy% (19867)------------------------------
% 1.75/0.60  % (19867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.60  % (19867)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.60  
% 1.75/0.60  % (19867)Memory used [KB]: 6268
% 1.75/0.60  % (19867)Time elapsed: 0.171 s
% 1.75/0.60  % (19867)------------------------------
% 1.75/0.60  % (19867)------------------------------
% 1.75/0.60  % (19871)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.75/0.60  % (19871)Refutation not found, incomplete strategy% (19871)------------------------------
% 1.75/0.60  % (19871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.60  % (19871)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.60  
% 1.75/0.60  % (19871)Memory used [KB]: 10746
% 1.75/0.60  % (19871)Time elapsed: 0.166 s
% 1.75/0.60  % (19871)------------------------------
% 1.75/0.60  % (19871)------------------------------
% 1.75/0.61  % (19886)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.75/0.62  % (19890)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.75/0.62  % (19891)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.75/0.62  % (19888)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.75/0.62  % (19880)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.75/0.62  % (19880)Refutation not found, incomplete strategy% (19880)------------------------------
% 1.75/0.62  % (19880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.62  % (19880)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.62  
% 1.75/0.62  % (19880)Memory used [KB]: 10618
% 1.75/0.62  % (19880)Time elapsed: 0.184 s
% 1.75/0.62  % (19880)------------------------------
% 1.75/0.62  % (19880)------------------------------
% 1.75/0.63  % (19883)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.75/0.63  % (19873)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.75/0.63  % (19883)Refutation not found, incomplete strategy% (19883)------------------------------
% 1.75/0.63  % (19883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.63  % (19883)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.63  
% 1.75/0.63  % (19883)Memory used [KB]: 10618
% 1.75/0.63  % (19883)Time elapsed: 0.198 s
% 1.75/0.63  % (19883)------------------------------
% 1.75/0.63  % (19883)------------------------------
% 1.75/0.63  % (19869)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.75/0.63  % (19873)Refutation not found, incomplete strategy% (19873)------------------------------
% 1.75/0.63  % (19873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.63  % (19873)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.63  
% 1.75/0.63  % (19873)Memory used [KB]: 10618
% 1.75/0.63  % (19873)Time elapsed: 0.196 s
% 1.75/0.63  % (19873)------------------------------
% 1.75/0.63  % (19873)------------------------------
% 1.75/0.63  % (19882)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.75/0.63  % (19875)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.75/0.64  % (19876)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.75/0.64  % (19878)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.75/0.64  % (19888)Refutation not found, incomplete strategy% (19888)------------------------------
% 1.75/0.64  % (19888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.64  % (19888)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.64  
% 1.75/0.64  % (19888)Memory used [KB]: 6268
% 1.75/0.64  % (19888)Time elapsed: 0.198 s
% 1.75/0.64  % (19888)------------------------------
% 1.75/0.64  % (19888)------------------------------
% 1.75/0.64  % (19878)Refutation not found, incomplete strategy% (19878)------------------------------
% 1.75/0.64  % (19878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.64  % (19878)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.64  
% 1.75/0.64  % (19878)Memory used [KB]: 6140
% 1.75/0.64  % (19878)Time elapsed: 0.003 s
% 1.75/0.64  % (19878)------------------------------
% 1.75/0.64  % (19878)------------------------------
% 1.75/0.64  % (19866)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.75/0.65  % (19870)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 2.17/0.66  % (19879)Refutation found. Thanks to Tanya!
% 2.17/0.66  % SZS status Theorem for theBenchmark
% 2.17/0.66  % SZS output start Proof for theBenchmark
% 2.17/0.66  fof(f996,plain,(
% 2.17/0.66    $false),
% 2.17/0.66    inference(avatar_sat_refutation,[],[f62,f67,f72,f163,f278,f993,f995])).
% 2.17/0.66  fof(f995,plain,(
% 2.17/0.66    spl2_2 | spl2_1 | ~spl2_14),
% 2.17/0.66    inference(avatar_split_clause,[],[f994,f990,f59,f64])).
% 2.17/0.66  fof(f64,plain,(
% 2.17/0.66    spl2_2 <=> k1_xboole_0 = sK0),
% 2.17/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.18/0.66  % (19877)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 2.18/0.66  fof(f59,plain,(
% 2.18/0.66    spl2_1 <=> sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.18/0.66  fof(f990,plain,(
% 2.18/0.66    spl2_14 <=> r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 2.18/0.66  fof(f994,plain,(
% 2.18/0.66    sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | ~spl2_14),
% 2.18/0.66    inference(resolution,[],[f992,f55])).
% 2.18/0.66  fof(f55,plain,(
% 2.18/0.66    ( ! [X0,X1] : (~r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 2.18/0.66    inference(definition_unfolding,[],[f34,f47,f47])).
% 2.18/0.66  fof(f47,plain,(
% 2.18/0.66    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 2.18/0.66    inference(definition_unfolding,[],[f26,f43])).
% 2.18/0.66  fof(f43,plain,(
% 2.18/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 2.18/0.66    inference(definition_unfolding,[],[f31,f42])).
% 2.18/0.67  fof(f42,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f37,f41])).
% 2.18/0.67  fof(f41,plain,(
% 2.18/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f39,f40])).
% 2.18/0.67  fof(f40,plain,(
% 2.18/0.67    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f13])).
% 2.18/0.67  fof(f13,axiom,(
% 2.18/0.67    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.18/0.67  fof(f39,plain,(
% 2.18/0.67    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f12])).
% 2.18/0.67  fof(f12,axiom,(
% 2.18/0.67    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.18/0.67  fof(f37,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f11])).
% 2.18/0.67  fof(f11,axiom,(
% 2.18/0.67    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.18/0.67  fof(f31,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f10])).
% 2.18/0.67  fof(f10,axiom,(
% 2.18/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.18/0.67  fof(f26,plain,(
% 2.18/0.67    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f9])).
% 2.18/0.67  fof(f9,axiom,(
% 2.18/0.67    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.18/0.67  fof(f34,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f14])).
% 2.18/0.67  fof(f14,axiom,(
% 2.18/0.67    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.18/0.67  fof(f992,plain,(
% 2.18/0.67    r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl2_14),
% 2.18/0.67    inference(avatar_component_clause,[],[f990])).
% 2.18/0.67  fof(f993,plain,(
% 2.18/0.67    spl2_14 | ~spl2_9),
% 2.18/0.67    inference(avatar_split_clause,[],[f986,f275,f990])).
% 2.18/0.67  fof(f275,plain,(
% 2.18/0.67    spl2_9 <=> k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))),
% 2.18/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 2.18/0.67  fof(f986,plain,(
% 2.18/0.67    r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) | ~spl2_9),
% 2.18/0.67    inference(superposition,[],[f52,f277])).
% 2.18/0.67  fof(f277,plain,(
% 2.18/0.67    k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))) | ~spl2_9),
% 2.18/0.67    inference(avatar_component_clause,[],[f275])).
% 2.18/0.67  fof(f52,plain,(
% 2.18/0.67    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 2.18/0.67    inference(definition_unfolding,[],[f29,f44])).
% 2.18/0.67  fof(f44,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 2.18/0.67    inference(definition_unfolding,[],[f30,f43])).
% 2.18/0.67  fof(f30,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f15])).
% 2.18/0.67  fof(f15,axiom,(
% 2.18/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.18/0.67  fof(f29,plain,(
% 2.18/0.67    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f5])).
% 2.18/0.67  fof(f5,axiom,(
% 2.18/0.67    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.18/0.67  fof(f278,plain,(
% 2.18/0.67    spl2_9 | ~spl2_4),
% 2.18/0.67    inference(avatar_split_clause,[],[f273,f160,f275])).
% 2.18/0.67  fof(f160,plain,(
% 2.18/0.67    spl2_4 <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))))))),
% 2.18/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.18/0.67  fof(f273,plain,(
% 2.18/0.67    k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) = k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))) | ~spl2_4),
% 2.18/0.67    inference(forward_demodulation,[],[f272,f25])).
% 2.18/0.67  fof(f25,plain,(
% 2.18/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.18/0.67    inference(cnf_transformation,[],[f4])).
% 2.18/0.67  fof(f4,axiom,(
% 2.18/0.67    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.18/0.67  fof(f272,plain,(
% 2.18/0.67    k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) | ~spl2_4),
% 2.18/0.67    inference(forward_demodulation,[],[f258,f96])).
% 2.18/0.67  fof(f96,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.18/0.67    inference(backward_demodulation,[],[f74,f90])).
% 2.18/0.67  fof(f90,plain,(
% 2.18/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.18/0.67    inference(forward_demodulation,[],[f83,f25])).
% 2.18/0.67  fof(f83,plain,(
% 2.18/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.18/0.67    inference(superposition,[],[f74,f24])).
% 2.18/0.67  fof(f24,plain,(
% 2.18/0.67    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f7])).
% 2.18/0.67  fof(f7,axiom,(
% 2.18/0.67    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.18/0.67  fof(f74,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.18/0.67    inference(superposition,[],[f38,f24])).
% 2.18/0.67  fof(f38,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f6])).
% 2.18/0.67  fof(f6,axiom,(
% 2.18/0.67    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.18/0.67  fof(f258,plain,(
% 2.18/0.67    k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0))) | ~spl2_4),
% 2.18/0.67    inference(superposition,[],[f226,f24])).
% 2.18/0.67  fof(f226,plain,(
% 2.18/0.67    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),X0)))) = X0) ) | ~spl2_4),
% 2.18/0.67    inference(forward_demodulation,[],[f225,f90])).
% 2.18/0.67  fof(f225,plain,(
% 2.18/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),X0))))) ) | ~spl2_4),
% 2.18/0.67    inference(forward_demodulation,[],[f224,f38])).
% 2.18/0.67  fof(f224,plain,(
% 2.18/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))),X0)))) ) | ~spl2_4),
% 2.18/0.67    inference(forward_demodulation,[],[f199,f38])).
% 2.18/0.67  fof(f199,plain,(
% 2.18/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))))),X0))) ) | ~spl2_4),
% 2.18/0.67    inference(superposition,[],[f38,f162])).
% 2.18/0.67  fof(f162,plain,(
% 2.18/0.67    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))))) | ~spl2_4),
% 2.18/0.67    inference(avatar_component_clause,[],[f160])).
% 2.18/0.67  fof(f163,plain,(
% 2.18/0.67    spl2_4 | ~spl2_3),
% 2.18/0.67    inference(avatar_split_clause,[],[f158,f69,f160])).
% 2.18/0.67  fof(f69,plain,(
% 2.18/0.67    spl2_3 <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))))),
% 2.18/0.67    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.18/0.67  fof(f158,plain,(
% 2.18/0.67    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))))) | ~spl2_3),
% 2.18/0.67    inference(forward_demodulation,[],[f71,f38])).
% 2.18/0.67  fof(f71,plain,(
% 2.18/0.67    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))))) | ~spl2_3),
% 2.18/0.67    inference(avatar_component_clause,[],[f69])).
% 2.18/0.67  fof(f72,plain,(
% 2.18/0.67    spl2_3),
% 2.18/0.67    inference(avatar_split_clause,[],[f49,f69])).
% 2.18/0.67  fof(f49,plain,(
% 2.18/0.67    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))))),
% 2.18/0.67    inference(definition_unfolding,[],[f21,f46,f47])).
% 2.18/0.67  fof(f46,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) )),
% 2.18/0.67    inference(definition_unfolding,[],[f32,f45])).
% 2.18/0.67  fof(f45,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 2.18/0.67    inference(definition_unfolding,[],[f33,f44])).
% 2.18/0.67  fof(f33,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f8])).
% 2.18/0.67  fof(f8,axiom,(
% 2.18/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.18/0.67  fof(f32,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f3])).
% 2.18/0.67  fof(f3,axiom,(
% 2.18/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.18/0.67  fof(f21,plain,(
% 2.18/0.67    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 2.18/0.67    inference(cnf_transformation,[],[f20])).
% 2.18/0.67  fof(f20,plain,(
% 2.18/0.67    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 2.18/0.67    inference(ennf_transformation,[],[f17])).
% 2.18/0.67  fof(f17,negated_conjecture,(
% 2.18/0.67    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 2.18/0.67    inference(negated_conjecture,[],[f16])).
% 2.18/0.67  fof(f16,conjecture,(
% 2.18/0.67    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 2.18/0.67  fof(f67,plain,(
% 2.18/0.67    ~spl2_2),
% 2.18/0.67    inference(avatar_split_clause,[],[f22,f64])).
% 2.18/0.67  fof(f22,plain,(
% 2.18/0.67    k1_xboole_0 != sK0),
% 2.18/0.67    inference(cnf_transformation,[],[f20])).
% 2.18/0.67  fof(f62,plain,(
% 2.18/0.67    ~spl2_1),
% 2.18/0.67    inference(avatar_split_clause,[],[f48,f59])).
% 2.18/0.67  fof(f48,plain,(
% 2.18/0.67    sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)),
% 2.18/0.67    inference(definition_unfolding,[],[f23,f47])).
% 2.18/0.67  fof(f23,plain,(
% 2.18/0.67    sK0 != k1_tarski(sK1)),
% 2.18/0.67    inference(cnf_transformation,[],[f20])).
% 2.18/0.67  % SZS output end Proof for theBenchmark
% 2.18/0.67  % (19879)------------------------------
% 2.18/0.67  % (19879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.67  % (19879)Termination reason: Refutation
% 2.18/0.67  
% 2.18/0.67  % (19879)Memory used [KB]: 11513
% 2.18/0.67  % (19892)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 2.18/0.67  % (19879)Time elapsed: 0.208 s
% 2.18/0.67  % (19879)------------------------------
% 2.18/0.67  % (19879)------------------------------
% 2.18/0.67  % (19862)Success in time 0.298 s
%------------------------------------------------------------------------------
