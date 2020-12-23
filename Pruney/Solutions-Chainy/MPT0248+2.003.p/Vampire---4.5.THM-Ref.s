%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:49 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 441 expanded)
%              Number of leaves         :   18 ( 146 expanded)
%              Depth                    :   15
%              Number of atoms          :  231 ( 952 expanded)
%              Number of equality atoms :  127 ( 730 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f233,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f73,f80,f113,f170,f174,f232])).

fof(f232,plain,
    ( ~ spl3_1
    | spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | spl3_5 ),
    inference(subsumption_resolution,[],[f230,f79])).

fof(f79,plain,
    ( sK1 != sK2
    | spl3_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f230,plain,
    ( sK1 = sK2
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f229,f63])).

fof(f63,plain,
    ( k1_xboole_0 != sK2
    | spl3_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f229,plain,
    ( k1_xboole_0 = sK2
    | sK1 = sK2
    | ~ spl3_1 ),
    inference(resolution,[],[f194,f223])).

fof(f223,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_1 ),
    inference(superposition,[],[f126,f217])).

fof(f217,plain,
    ( sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f45,f58])).

fof(f58,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_1
  <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f45,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f21,f41,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f39])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f126,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[],[f107,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f27,f39,f39])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f107,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(resolution,[],[f51,f52])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

% (13301)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (13285)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f194,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0
        | sK1 = X0 )
    | ~ spl3_1 ),
    inference(superposition,[],[f50,f58])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f34,f41,f41])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f174,plain,
    ( spl3_1
    | spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f135,f88,f66,f57])).

fof(f66,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f88,plain,
    ( spl3_6
  <=> r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f135,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f50,f89])).

fof(f89,plain,
    ( r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f170,plain,
    ( spl3_1
    | spl3_4
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl3_1
    | spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f168,f141])).

% (13293)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (13297)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f141,plain,
    ( k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_1
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f59,f136])).

fof(f136,plain,
    ( k1_xboole_0 = sK1
    | spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f135,f59])).

fof(f59,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f168,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_1
    | spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f165,f121])).

fof(f121,plain,(
    ! [X2] : k3_tarski(k2_enumset1(X2,X2,X2,k1_xboole_0)) = X2 ),
    inference(forward_demodulation,[],[f119,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f119,plain,(
    ! [X2] : k3_tarski(k2_enumset1(X2,X2,X2,k1_xboole_0)) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f47,f25])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X1) ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f165,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | spl3_1
    | spl3_4
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f140,f163])).

fof(f163,plain,
    ( k1_xboole_0 = sK2
    | spl3_1
    | spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f161,f72])).

fof(f72,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_4
  <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f161,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_1
    | ~ spl3_6 ),
    inference(resolution,[],[f157,f50])).

fof(f157,plain,
    ( r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl3_1
    | ~ spl3_6 ),
    inference(superposition,[],[f126,f140])).

fof(f140,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))
    | spl3_1
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f45,f136])).

fof(f113,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f111,f90])).

fof(f90,plain,
    ( ~ r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f111,plain,(
    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f110,f52])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),X0)
      | r1_tarski(sK1,X0) ) ),
    inference(superposition,[],[f51,f45])).

fof(f80,plain,
    ( ~ spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f75,f57,f77])).

fof(f75,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f74])).

fof(f74,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f44])).

fof(f44,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f22,f41,f41])).

fof(f22,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f43,f70,f66])).

fof(f43,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f23,f41])).

fof(f23,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f42,f61,f57])).

fof(f42,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f24,f41])).

fof(f24,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n009.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:21:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (13282)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.52/0.56  % (13282)Refutation found. Thanks to Tanya!
% 1.52/0.56  % SZS status Theorem for theBenchmark
% 1.52/0.56  % SZS output start Proof for theBenchmark
% 1.52/0.56  fof(f233,plain,(
% 1.52/0.56    $false),
% 1.52/0.56    inference(avatar_sat_refutation,[],[f64,f73,f80,f113,f170,f174,f232])).
% 1.52/0.56  fof(f232,plain,(
% 1.52/0.56    ~spl3_1 | spl3_2 | spl3_5),
% 1.52/0.56    inference(avatar_contradiction_clause,[],[f231])).
% 1.52/0.56  fof(f231,plain,(
% 1.52/0.56    $false | (~spl3_1 | spl3_2 | spl3_5)),
% 1.52/0.56    inference(subsumption_resolution,[],[f230,f79])).
% 1.52/0.56  fof(f79,plain,(
% 1.52/0.56    sK1 != sK2 | spl3_5),
% 1.52/0.56    inference(avatar_component_clause,[],[f77])).
% 1.52/0.56  fof(f77,plain,(
% 1.52/0.56    spl3_5 <=> sK1 = sK2),
% 1.52/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.52/0.56  fof(f230,plain,(
% 1.52/0.56    sK1 = sK2 | (~spl3_1 | spl3_2)),
% 1.52/0.56    inference(subsumption_resolution,[],[f229,f63])).
% 1.52/0.56  fof(f63,plain,(
% 1.52/0.56    k1_xboole_0 != sK2 | spl3_2),
% 1.52/0.56    inference(avatar_component_clause,[],[f61])).
% 1.52/0.56  fof(f61,plain,(
% 1.52/0.56    spl3_2 <=> k1_xboole_0 = sK2),
% 1.52/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.52/0.56  fof(f229,plain,(
% 1.52/0.56    k1_xboole_0 = sK2 | sK1 = sK2 | ~spl3_1),
% 1.52/0.56    inference(resolution,[],[f194,f223])).
% 1.52/0.56  fof(f223,plain,(
% 1.52/0.56    r1_tarski(sK2,sK1) | ~spl3_1),
% 1.52/0.56    inference(superposition,[],[f126,f217])).
% 1.52/0.56  fof(f217,plain,(
% 1.52/0.56    sK1 = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) | ~spl3_1),
% 1.52/0.56    inference(forward_demodulation,[],[f45,f58])).
% 1.52/0.56  fof(f58,plain,(
% 1.52/0.56    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_1),
% 1.52/0.56    inference(avatar_component_clause,[],[f57])).
% 1.52/0.56  fof(f57,plain,(
% 1.52/0.56    spl3_1 <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.52/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.52/0.56  fof(f45,plain,(
% 1.52/0.56    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.52/0.56    inference(definition_unfolding,[],[f21,f41,f40])).
% 1.52/0.56  fof(f40,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.52/0.56    inference(definition_unfolding,[],[f28,f39])).
% 1.52/0.56  fof(f39,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.52/0.56    inference(definition_unfolding,[],[f29,f37])).
% 1.52/0.56  fof(f37,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f8])).
% 1.52/0.56  fof(f8,axiom,(
% 1.52/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.52/0.56  fof(f29,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f7])).
% 1.52/0.56  fof(f7,axiom,(
% 1.52/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.52/0.56  fof(f28,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.52/0.56    inference(cnf_transformation,[],[f10])).
% 1.52/0.56  fof(f10,axiom,(
% 1.52/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.52/0.56  fof(f41,plain,(
% 1.52/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.52/0.56    inference(definition_unfolding,[],[f26,f39])).
% 1.52/0.56  fof(f26,plain,(
% 1.52/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f6])).
% 1.52/0.56  fof(f6,axiom,(
% 1.52/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.52/0.56  fof(f21,plain,(
% 1.52/0.56    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.52/0.56    inference(cnf_transformation,[],[f16])).
% 1.52/0.56  fof(f16,plain,(
% 1.52/0.56    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.52/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 1.52/0.56  fof(f15,plain,(
% 1.52/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.52/0.56    introduced(choice_axiom,[])).
% 1.52/0.56  fof(f13,plain,(
% 1.52/0.56    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.52/0.56    inference(ennf_transformation,[],[f12])).
% 1.52/0.56  fof(f12,negated_conjecture,(
% 1.52/0.56    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.52/0.56    inference(negated_conjecture,[],[f11])).
% 1.52/0.56  fof(f11,conjecture,(
% 1.52/0.56    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.52/0.56  fof(f126,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))) )),
% 1.52/0.56    inference(superposition,[],[f107,f46])).
% 1.52/0.56  fof(f46,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.52/0.56    inference(definition_unfolding,[],[f27,f39,f39])).
% 1.52/0.56  fof(f27,plain,(
% 1.52/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f5])).
% 1.52/0.56  fof(f5,axiom,(
% 1.52/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.52/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.52/0.56  fof(f107,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.52/0.56    inference(resolution,[],[f51,f52])).
% 1.52/0.56  fof(f52,plain,(
% 1.52/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.52/0.56    inference(equality_resolution,[],[f32])).
% 1.52/0.56  fof(f32,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.52/0.56    inference(cnf_transformation,[],[f18])).
% 1.52/0.56  fof(f18,plain,(
% 1.52/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.56    inference(flattening,[],[f17])).
% 1.52/0.57  % (13301)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.52/0.57  % (13285)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.52/0.57  fof(f17,plain,(
% 1.52/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.57    inference(nnf_transformation,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.52/0.57  fof(f51,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f38,f40])).
% 1.52/0.57  fof(f38,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f14])).
% 1.52/0.57  fof(f14,plain,(
% 1.52/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.52/0.57    inference(ennf_transformation,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.52/0.57  fof(f194,plain,(
% 1.52/0.57    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | sK1 = X0) ) | ~spl3_1),
% 1.52/0.57    inference(superposition,[],[f50,f58])).
% 1.52/0.57  fof(f50,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.52/0.57    inference(definition_unfolding,[],[f34,f41,f41])).
% 1.52/0.57  fof(f34,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.52/0.57    inference(cnf_transformation,[],[f20])).
% 1.52/0.57  fof(f20,plain,(
% 1.52/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.52/0.57    inference(flattening,[],[f19])).
% 1.52/0.57  fof(f19,plain,(
% 1.52/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.52/0.57    inference(nnf_transformation,[],[f9])).
% 1.52/0.57  fof(f9,axiom,(
% 1.52/0.57    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.52/0.57  fof(f174,plain,(
% 1.52/0.57    spl3_1 | spl3_3 | ~spl3_6),
% 1.52/0.57    inference(avatar_split_clause,[],[f135,f88,f66,f57])).
% 1.52/0.57  fof(f66,plain,(
% 1.52/0.57    spl3_3 <=> k1_xboole_0 = sK1),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.52/0.57  fof(f88,plain,(
% 1.52/0.57    spl3_6 <=> r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.52/0.57  fof(f135,plain,(
% 1.52/0.57    k1_xboole_0 = sK1 | sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_6),
% 1.52/0.57    inference(resolution,[],[f50,f89])).
% 1.52/0.57  fof(f89,plain,(
% 1.52/0.57    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_6),
% 1.52/0.57    inference(avatar_component_clause,[],[f88])).
% 1.52/0.57  fof(f170,plain,(
% 1.52/0.57    spl3_1 | spl3_4 | ~spl3_6),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f169])).
% 1.52/0.57  fof(f169,plain,(
% 1.52/0.57    $false | (spl3_1 | spl3_4 | ~spl3_6)),
% 1.52/0.57    inference(subsumption_resolution,[],[f168,f141])).
% 1.52/0.57  % (13293)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.52/0.57  % (13297)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.52/0.57  fof(f141,plain,(
% 1.52/0.57    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) | (spl3_1 | ~spl3_6)),
% 1.52/0.57    inference(backward_demodulation,[],[f59,f136])).
% 1.52/0.57  fof(f136,plain,(
% 1.52/0.57    k1_xboole_0 = sK1 | (spl3_1 | ~spl3_6)),
% 1.52/0.57    inference(subsumption_resolution,[],[f135,f59])).
% 1.52/0.57  fof(f59,plain,(
% 1.52/0.57    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | spl3_1),
% 1.52/0.57    inference(avatar_component_clause,[],[f57])).
% 1.52/0.57  fof(f168,plain,(
% 1.52/0.57    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | (spl3_1 | spl3_4 | ~spl3_6)),
% 1.52/0.57    inference(forward_demodulation,[],[f165,f121])).
% 1.52/0.57  fof(f121,plain,(
% 1.52/0.57    ( ! [X2] : (k3_tarski(k2_enumset1(X2,X2,X2,k1_xboole_0)) = X2) )),
% 1.52/0.57    inference(forward_demodulation,[],[f119,f25])).
% 1.52/0.57  fof(f25,plain,(
% 1.52/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f3])).
% 1.52/0.57  fof(f3,axiom,(
% 1.52/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.52/0.57  fof(f119,plain,(
% 1.52/0.57    ( ! [X2] : (k3_tarski(k2_enumset1(X2,X2,X2,k1_xboole_0)) = k4_xboole_0(X2,k1_xboole_0)) )),
% 1.52/0.57    inference(superposition,[],[f47,f25])).
% 1.52/0.57  fof(f47,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_enumset1(X0,X0,X0,X1)),X1)) )),
% 1.52/0.57    inference(definition_unfolding,[],[f30,f40])).
% 1.52/0.57  fof(f30,plain,(
% 1.52/0.57    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f4])).
% 1.52/0.57  fof(f4,axiom,(
% 1.52/0.57    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.52/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.52/0.57  fof(f165,plain,(
% 1.52/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | (spl3_1 | spl3_4 | ~spl3_6)),
% 1.52/0.57    inference(backward_demodulation,[],[f140,f163])).
% 1.52/0.57  fof(f163,plain,(
% 1.52/0.57    k1_xboole_0 = sK2 | (spl3_1 | spl3_4 | ~spl3_6)),
% 1.52/0.57    inference(subsumption_resolution,[],[f161,f72])).
% 1.52/0.57  fof(f72,plain,(
% 1.52/0.57    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | spl3_4),
% 1.52/0.57    inference(avatar_component_clause,[],[f70])).
% 1.52/0.57  fof(f70,plain,(
% 1.52/0.57    spl3_4 <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.52/0.57  fof(f161,plain,(
% 1.52/0.57    k1_xboole_0 = sK2 | sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | (spl3_1 | ~spl3_6)),
% 1.52/0.57    inference(resolution,[],[f157,f50])).
% 1.52/0.57  fof(f157,plain,(
% 1.52/0.57    r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | (spl3_1 | ~spl3_6)),
% 1.52/0.57    inference(superposition,[],[f126,f140])).
% 1.52/0.57  fof(f140,plain,(
% 1.52/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) | (spl3_1 | ~spl3_6)),
% 1.52/0.57    inference(backward_demodulation,[],[f45,f136])).
% 1.52/0.57  fof(f113,plain,(
% 1.52/0.57    spl3_6),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f112])).
% 1.52/0.57  fof(f112,plain,(
% 1.52/0.57    $false | spl3_6),
% 1.52/0.57    inference(subsumption_resolution,[],[f111,f90])).
% 1.52/0.57  fof(f90,plain,(
% 1.52/0.57    ~r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | spl3_6),
% 1.52/0.57    inference(avatar_component_clause,[],[f88])).
% 1.52/0.57  fof(f111,plain,(
% 1.52/0.57    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.52/0.57    inference(resolution,[],[f110,f52])).
% 1.52/0.57  fof(f110,plain,(
% 1.52/0.57    ( ! [X0] : (~r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),X0) | r1_tarski(sK1,X0)) )),
% 1.52/0.57    inference(superposition,[],[f51,f45])).
% 1.52/0.57  fof(f80,plain,(
% 1.52/0.57    ~spl3_5 | ~spl3_1),
% 1.52/0.57    inference(avatar_split_clause,[],[f75,f57,f77])).
% 1.52/0.57  fof(f75,plain,(
% 1.52/0.57    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != sK2),
% 1.52/0.57    inference(inner_rewriting,[],[f74])).
% 1.52/0.57  fof(f74,plain,(
% 1.52/0.57    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != sK2),
% 1.52/0.57    inference(inner_rewriting,[],[f44])).
% 1.52/0.57  fof(f44,plain,(
% 1.52/0.57    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.52/0.57    inference(definition_unfolding,[],[f22,f41,f41])).
% 1.52/0.57  fof(f22,plain,(
% 1.52/0.57    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  fof(f73,plain,(
% 1.52/0.57    ~spl3_3 | ~spl3_4),
% 1.52/0.57    inference(avatar_split_clause,[],[f43,f70,f66])).
% 1.52/0.57  fof(f43,plain,(
% 1.52/0.57    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.52/0.57    inference(definition_unfolding,[],[f23,f41])).
% 1.52/0.57  fof(f23,plain,(
% 1.52/0.57    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  fof(f64,plain,(
% 1.52/0.57    ~spl3_1 | ~spl3_2),
% 1.52/0.57    inference(avatar_split_clause,[],[f42,f61,f57])).
% 1.52/0.57  fof(f42,plain,(
% 1.52/0.57    k1_xboole_0 != sK2 | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.52/0.57    inference(definition_unfolding,[],[f24,f41])).
% 1.52/0.57  fof(f24,plain,(
% 1.52/0.57    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  % SZS output end Proof for theBenchmark
% 1.52/0.57  % (13282)------------------------------
% 1.52/0.57  % (13282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (13282)Termination reason: Refutation
% 1.52/0.57  
% 1.52/0.57  % (13282)Memory used [KB]: 10746
% 1.52/0.57  % (13282)Time elapsed: 0.124 s
% 1.52/0.57  % (13282)------------------------------
% 1.52/0.57  % (13282)------------------------------
% 1.52/0.57  % (13275)Success in time 0.214 s
%------------------------------------------------------------------------------
