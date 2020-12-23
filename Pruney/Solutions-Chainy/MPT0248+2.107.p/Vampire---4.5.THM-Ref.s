%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:05 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 556 expanded)
%              Number of leaves         :   19 ( 190 expanded)
%              Depth                    :   14
%              Number of atoms          :  195 ( 855 expanded)
%              Number of equality atoms :   93 ( 695 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f273,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f89,f99,f167,f244,f272])).

fof(f272,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f269])).

fof(f269,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f54,f260])).

% (11898)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f260,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(forward_demodulation,[],[f248,f77])).

fof(f77,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f47,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f23,f28])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f248,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(superposition,[],[f203,f74])).

fof(f74,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f203,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_xboole_0,sK2),k1_xboole_0)
    | ~ spl3_3
    | spl3_5 ),
    inference(superposition,[],[f174,f202])).

fof(f202,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,sK2)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f168,f94])).

fof(f94,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f91,f77])).

fof(f91,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f49,f22])).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f29,f41,f28])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f26,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f168,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl3_3 ),
    inference(superposition,[],[f43,f69])).

fof(f69,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f43,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f21,f42,f41])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f40])).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f174,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0)
    | ~ spl3_3
    | spl3_5 ),
    inference(forward_demodulation,[],[f88,f69])).

fof(f88,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_5
  <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f244,plain,
    ( spl3_1
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f54,f75,f207,f226])).

fof(f226,plain,
    ( ! [X0] :
        ( k5_xboole_0(k1_xboole_0,sK2) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f208,f177])).

fof(f177,plain,(
    ! [X2,X1] :
      ( r1_tarski(X2,k5_xboole_0(k1_xboole_0,X1))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f53,f94])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f208,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k5_xboole_0(k1_xboole_0,sK2))
        | k5_xboole_0(k1_xboole_0,sK2) = X1
        | k1_xboole_0 = X1 )
    | ~ spl3_3 ),
    inference(superposition,[],[f52,f202])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f33,f42,f42])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f207,plain,
    ( sK2 != k5_xboole_0(k1_xboole_0,sK2)
    | spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f61,f202])).

fof(f61,plain,
    ( sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_1
  <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f75,plain,
    ( k1_xboole_0 != sK2
    | spl3_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f167,plain,
    ( spl3_1
    | ~ spl3_2
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f75,f135,f152,f136])).

fof(f136,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK1)
        | sK1 = X1
        | k1_xboole_0 = X1 )
    | ~ spl3_2 ),
    inference(superposition,[],[f52,f64])).

fof(f64,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_2
  <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f152,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f133,f54])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_tarski(X0,sK1) )
    | ~ spl3_2 ),
    inference(superposition,[],[f82,f64])).

fof(f82,plain,(
    ! [X0] :
      ( r1_tarski(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f53,f43])).

fof(f135,plain,
    ( sK1 != sK2
    | spl3_1
    | ~ spl3_2 ),
    inference(superposition,[],[f61,f64])).

fof(f99,plain,
    ( spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f98,f63,f68])).

fof(f98,plain,
    ( sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f52,f83])).

fof(f83,plain,(
    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f48,f43])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f25,f41])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f89,plain,
    ( spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f84,f86,f63])).

fof(f84,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)
    | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f83,f32])).

% (11905)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f76,plain,
    ( ~ spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f46,f63,f73])).

fof(f46,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f18,f42])).

fof(f18,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f71,plain,
    ( ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f45,f68,f59])).

fof(f45,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f19,f42])).

fof(f19,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f44,f63,f59])).

fof(f44,plain,
    ( sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f20,f42,f42])).

fof(f20,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.07/0.26  % Computer   : n022.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 09:57:25 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.11/0.36  % (11882)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.11/0.36  % (11880)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.11/0.36  % (11900)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.11/0.37  % (11888)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.11/0.37  % (11906)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.11/0.37  % (11891)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.11/0.37  % (11894)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.11/0.37  % (11892)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.11/0.37  % (11893)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.11/0.37  % (11894)Refutation not found, incomplete strategy% (11894)------------------------------
% 0.11/0.37  % (11894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.37  % (11894)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.37  
% 0.11/0.37  % (11894)Memory used [KB]: 1791
% 0.11/0.37  % (11894)Time elapsed: 0.069 s
% 0.11/0.37  % (11894)------------------------------
% 0.11/0.37  % (11894)------------------------------
% 0.11/0.37  % (11893)Refutation found. Thanks to Tanya!
% 0.11/0.37  % SZS status Theorem for theBenchmark
% 0.11/0.38  % (11881)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.11/0.38  % (11886)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.11/0.38  % (11881)Refutation not found, incomplete strategy% (11881)------------------------------
% 0.11/0.38  % (11881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.38  % (11881)Termination reason: Refutation not found, incomplete strategy
% 0.11/0.38  
% 0.11/0.38  % (11881)Memory used [KB]: 1791
% 0.11/0.38  % (11881)Time elapsed: 0.090 s
% 0.11/0.38  % (11881)------------------------------
% 0.11/0.38  % (11881)------------------------------
% 0.11/0.39  % (11904)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.11/0.39  % (11885)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.11/0.39  % SZS output start Proof for theBenchmark
% 0.11/0.39  fof(f273,plain,(
% 0.11/0.39    $false),
% 0.11/0.39    inference(avatar_sat_refutation,[],[f66,f71,f76,f89,f99,f167,f244,f272])).
% 0.11/0.39  fof(f272,plain,(
% 0.11/0.39    ~spl3_3 | ~spl3_4 | spl3_5),
% 0.11/0.39    inference(avatar_contradiction_clause,[],[f269])).
% 0.11/0.39  fof(f269,plain,(
% 0.11/0.39    $false | (~spl3_3 | ~spl3_4 | spl3_5)),
% 0.11/0.39    inference(unit_resulting_resolution,[],[f54,f260])).
% 0.11/0.39  % (11898)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.11/0.39  fof(f260,plain,(
% 0.11/0.39    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl3_3 | ~spl3_4 | spl3_5)),
% 0.11/0.39    inference(forward_demodulation,[],[f248,f77])).
% 0.11/0.39  fof(f77,plain,(
% 0.11/0.39    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.11/0.39    inference(forward_demodulation,[],[f47,f22])).
% 0.11/0.39  fof(f22,plain,(
% 0.11/0.39    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f4])).
% 0.11/0.39  fof(f4,axiom,(
% 0.11/0.39    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.11/0.39  fof(f47,plain,(
% 0.11/0.39    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.11/0.39    inference(definition_unfolding,[],[f23,f28])).
% 0.11/0.39  fof(f28,plain,(
% 0.11/0.39    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.11/0.39    inference(cnf_transformation,[],[f2])).
% 0.11/0.39  fof(f2,axiom,(
% 0.11/0.39    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.11/0.39  fof(f23,plain,(
% 0.11/0.39    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.11/0.39    inference(cnf_transformation,[],[f5])).
% 0.11/0.39  fof(f5,axiom,(
% 0.11/0.39    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.11/0.39  fof(f248,plain,(
% 0.11/0.39    ~r1_tarski(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl3_3 | ~spl3_4 | spl3_5)),
% 0.11/0.39    inference(superposition,[],[f203,f74])).
% 0.11/0.39  fof(f74,plain,(
% 0.11/0.39    k1_xboole_0 = sK2 | ~spl3_4),
% 0.11/0.39    inference(avatar_component_clause,[],[f73])).
% 0.11/0.39  fof(f73,plain,(
% 0.11/0.39    spl3_4 <=> k1_xboole_0 = sK2),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.11/0.39  fof(f203,plain,(
% 0.11/0.39    ~r1_tarski(k5_xboole_0(k1_xboole_0,sK2),k1_xboole_0) | (~spl3_3 | spl3_5)),
% 0.11/0.39    inference(superposition,[],[f174,f202])).
% 0.11/0.39  fof(f202,plain,(
% 0.11/0.39    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,sK2) | ~spl3_3),
% 0.11/0.39    inference(forward_demodulation,[],[f168,f94])).
% 0.11/0.39  fof(f94,plain,(
% 0.11/0.39    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.11/0.39    inference(forward_demodulation,[],[f91,f77])).
% 0.11/0.39  fof(f91,plain,(
% 0.11/0.39    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) )),
% 0.11/0.39    inference(superposition,[],[f49,f22])).
% 0.11/0.39  fof(f49,plain,(
% 0.11/0.39    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.11/0.39    inference(definition_unfolding,[],[f29,f41,f28])).
% 0.11/0.39  fof(f41,plain,(
% 0.11/0.39    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.11/0.39    inference(definition_unfolding,[],[f26,f40])).
% 0.11/0.39  fof(f40,plain,(
% 0.11/0.39    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.11/0.39    inference(definition_unfolding,[],[f27,f39])).
% 0.11/0.39  fof(f39,plain,(
% 0.11/0.39    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.11/0.39    inference(definition_unfolding,[],[f36,f38])).
% 0.11/0.39  fof(f38,plain,(
% 0.11/0.39    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f11])).
% 0.11/0.39  fof(f11,axiom,(
% 0.11/0.39    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.11/0.39  fof(f36,plain,(
% 0.11/0.39    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f10])).
% 0.11/0.39  fof(f10,axiom,(
% 0.11/0.39    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.11/0.39  fof(f27,plain,(
% 0.11/0.39    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f9])).
% 0.11/0.39  fof(f9,axiom,(
% 0.11/0.39    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.11/0.39  fof(f26,plain,(
% 0.11/0.39    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.11/0.39    inference(cnf_transformation,[],[f13])).
% 0.11/0.39  fof(f13,axiom,(
% 0.11/0.39    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.11/0.39  fof(f29,plain,(
% 0.11/0.39    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.11/0.39    inference(cnf_transformation,[],[f7])).
% 0.11/0.39  fof(f7,axiom,(
% 0.11/0.39    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.11/0.39  fof(f168,plain,(
% 0.11/0.39    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) | ~spl3_3),
% 0.11/0.39    inference(superposition,[],[f43,f69])).
% 0.11/0.39  fof(f69,plain,(
% 0.11/0.39    k1_xboole_0 = sK1 | ~spl3_3),
% 0.11/0.39    inference(avatar_component_clause,[],[f68])).
% 0.11/0.39  fof(f68,plain,(
% 0.11/0.39    spl3_3 <=> k1_xboole_0 = sK1),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.11/0.39  fof(f43,plain,(
% 0.11/0.39    k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK2))),
% 0.11/0.39    inference(definition_unfolding,[],[f21,f42,f41])).
% 0.11/0.39  fof(f42,plain,(
% 0.11/0.39    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.11/0.39    inference(definition_unfolding,[],[f24,f40])).
% 0.11/0.39  fof(f24,plain,(
% 0.11/0.39    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.11/0.39    inference(cnf_transformation,[],[f8])).
% 0.11/0.39  fof(f8,axiom,(
% 0.11/0.39    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.11/0.39  fof(f21,plain,(
% 0.11/0.39    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.11/0.39    inference(cnf_transformation,[],[f16])).
% 0.11/0.39  fof(f16,plain,(
% 0.11/0.39    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.11/0.39    inference(ennf_transformation,[],[f15])).
% 0.11/0.39  fof(f15,negated_conjecture,(
% 0.11/0.39    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.11/0.39    inference(negated_conjecture,[],[f14])).
% 0.11/0.39  fof(f14,conjecture,(
% 0.11/0.39    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.11/0.39  fof(f174,plain,(
% 0.11/0.39    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k1_xboole_0) | (~spl3_3 | spl3_5)),
% 0.11/0.39    inference(forward_demodulation,[],[f88,f69])).
% 0.11/0.39  fof(f88,plain,(
% 0.11/0.39    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | spl3_5),
% 0.11/0.39    inference(avatar_component_clause,[],[f86])).
% 0.11/0.39  fof(f86,plain,(
% 0.11/0.39    spl3_5 <=> r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.11/0.39  fof(f54,plain,(
% 0.11/0.39    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.11/0.39    inference(equality_resolution,[],[f31])).
% 0.11/0.39  fof(f31,plain,(
% 0.11/0.39    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.11/0.39    inference(cnf_transformation,[],[f1])).
% 0.11/0.39  fof(f1,axiom,(
% 0.11/0.39    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.11/0.39  fof(f244,plain,(
% 0.11/0.39    spl3_1 | ~spl3_3 | spl3_4),
% 0.11/0.39    inference(avatar_contradiction_clause,[],[f229])).
% 0.11/0.39  fof(f229,plain,(
% 0.11/0.39    $false | (spl3_1 | ~spl3_3 | spl3_4)),
% 0.11/0.39    inference(unit_resulting_resolution,[],[f54,f75,f207,f226])).
% 0.11/0.39  fof(f226,plain,(
% 0.11/0.39    ( ! [X0] : (k5_xboole_0(k1_xboole_0,sK2) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,sK2)) ) | ~spl3_3),
% 0.11/0.39    inference(resolution,[],[f208,f177])).
% 0.11/0.39  fof(f177,plain,(
% 0.11/0.39    ( ! [X2,X1] : (r1_tarski(X2,k5_xboole_0(k1_xboole_0,X1)) | ~r1_tarski(X2,X1)) )),
% 0.11/0.39    inference(superposition,[],[f53,f94])).
% 0.11/0.39  fof(f53,plain,(
% 0.11/0.39    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.11/0.39    inference(definition_unfolding,[],[f37,f41])).
% 0.11/0.39  fof(f37,plain,(
% 0.11/0.39    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 0.11/0.39    inference(cnf_transformation,[],[f17])).
% 0.11/0.39  fof(f17,plain,(
% 0.11/0.39    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.11/0.39    inference(ennf_transformation,[],[f3])).
% 0.11/0.39  fof(f3,axiom,(
% 0.11/0.39    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.11/0.39  fof(f208,plain,(
% 0.11/0.39    ( ! [X1] : (~r1_tarski(X1,k5_xboole_0(k1_xboole_0,sK2)) | k5_xboole_0(k1_xboole_0,sK2) = X1 | k1_xboole_0 = X1) ) | ~spl3_3),
% 0.11/0.39    inference(superposition,[],[f52,f202])).
% 0.11/0.39  fof(f52,plain,(
% 0.11/0.39    ( ! [X0,X1] : (~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.11/0.39    inference(definition_unfolding,[],[f33,f42,f42])).
% 0.11/0.39  fof(f33,plain,(
% 0.11/0.39    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.11/0.39    inference(cnf_transformation,[],[f12])).
% 0.11/0.39  fof(f12,axiom,(
% 0.11/0.39    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.11/0.39  fof(f207,plain,(
% 0.11/0.39    sK2 != k5_xboole_0(k1_xboole_0,sK2) | (spl3_1 | ~spl3_3)),
% 0.11/0.39    inference(superposition,[],[f61,f202])).
% 0.11/0.39  fof(f61,plain,(
% 0.11/0.39    sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | spl3_1),
% 0.11/0.39    inference(avatar_component_clause,[],[f59])).
% 0.11/0.39  fof(f59,plain,(
% 0.11/0.39    spl3_1 <=> sK2 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.11/0.39  fof(f75,plain,(
% 0.11/0.39    k1_xboole_0 != sK2 | spl3_4),
% 0.11/0.39    inference(avatar_component_clause,[],[f73])).
% 0.11/0.39  fof(f167,plain,(
% 0.11/0.39    spl3_1 | ~spl3_2 | spl3_4),
% 0.11/0.39    inference(avatar_contradiction_clause,[],[f163])).
% 0.11/0.39  fof(f163,plain,(
% 0.11/0.39    $false | (spl3_1 | ~spl3_2 | spl3_4)),
% 0.11/0.39    inference(unit_resulting_resolution,[],[f75,f135,f152,f136])).
% 0.11/0.39  fof(f136,plain,(
% 0.11/0.39    ( ! [X1] : (~r1_tarski(X1,sK1) | sK1 = X1 | k1_xboole_0 = X1) ) | ~spl3_2),
% 0.11/0.39    inference(superposition,[],[f52,f64])).
% 0.11/0.39  fof(f64,plain,(
% 0.11/0.39    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | ~spl3_2),
% 0.11/0.39    inference(avatar_component_clause,[],[f63])).
% 0.11/0.39  fof(f63,plain,(
% 0.11/0.39    spl3_2 <=> sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.11/0.39    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.11/0.39  fof(f152,plain,(
% 0.11/0.39    r1_tarski(sK2,sK1) | ~spl3_2),
% 0.11/0.39    inference(resolution,[],[f133,f54])).
% 0.11/0.39  fof(f133,plain,(
% 0.11/0.39    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(X0,sK1)) ) | ~spl3_2),
% 0.11/0.39    inference(superposition,[],[f82,f64])).
% 0.11/0.39  fof(f82,plain,(
% 0.11/0.39    ( ! [X0] : (r1_tarski(X0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | ~r1_tarski(X0,sK2)) )),
% 0.11/0.39    inference(superposition,[],[f53,f43])).
% 0.11/0.39  fof(f135,plain,(
% 0.11/0.39    sK1 != sK2 | (spl3_1 | ~spl3_2)),
% 0.11/0.39    inference(superposition,[],[f61,f64])).
% 0.11/0.39  fof(f99,plain,(
% 0.11/0.39    spl3_3 | spl3_2),
% 0.11/0.39    inference(avatar_split_clause,[],[f98,f63,f68])).
% 0.11/0.39  fof(f98,plain,(
% 0.11/0.39    sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1),
% 0.11/0.39    inference(resolution,[],[f52,f83])).
% 0.11/0.39  fof(f83,plain,(
% 0.11/0.39    r1_tarski(sK1,k3_enumset1(sK0,sK0,sK0,sK0,sK0))),
% 0.11/0.39    inference(superposition,[],[f48,f43])).
% 0.11/0.39  fof(f48,plain,(
% 0.11/0.39    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.11/0.39    inference(definition_unfolding,[],[f25,f41])).
% 0.11/0.39  fof(f25,plain,(
% 0.11/0.39    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.11/0.39    inference(cnf_transformation,[],[f6])).
% 0.11/0.39  fof(f6,axiom,(
% 0.11/0.39    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.11/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.11/0.39  fof(f89,plain,(
% 0.11/0.39    spl3_2 | ~spl3_5),
% 0.11/0.39    inference(avatar_split_clause,[],[f84,f86,f63])).
% 0.11/0.39  fof(f84,plain,(
% 0.11/0.39    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),sK1) | sK1 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.11/0.39    inference(resolution,[],[f83,f32])).
% 0.11/0.39  % (11905)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.11/0.39  fof(f32,plain,(
% 0.11/0.39    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.11/0.39    inference(cnf_transformation,[],[f1])).
% 0.11/0.39  fof(f76,plain,(
% 0.11/0.39    ~spl3_4 | ~spl3_2),
% 0.11/0.39    inference(avatar_split_clause,[],[f46,f63,f73])).
% 0.11/0.39  fof(f46,plain,(
% 0.11/0.39    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 0.11/0.39    inference(definition_unfolding,[],[f18,f42])).
% 0.11/0.39  fof(f18,plain,(
% 0.11/0.39    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 0.11/0.39    inference(cnf_transformation,[],[f16])).
% 0.11/0.39  fof(f71,plain,(
% 0.11/0.39    ~spl3_1 | ~spl3_3),
% 0.11/0.39    inference(avatar_split_clause,[],[f45,f68,f59])).
% 0.11/0.39  fof(f45,plain,(
% 0.11/0.39    k1_xboole_0 != sK1 | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.11/0.39    inference(definition_unfolding,[],[f19,f42])).
% 0.11/0.39  fof(f19,plain,(
% 0.11/0.39    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 0.11/0.39    inference(cnf_transformation,[],[f16])).
% 0.11/0.39  fof(f66,plain,(
% 0.11/0.39    ~spl3_1 | ~spl3_2),
% 0.11/0.39    inference(avatar_split_clause,[],[f44,f63,f59])).
% 0.11/0.39  fof(f44,plain,(
% 0.11/0.39    sK1 != k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK2 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.11/0.39    inference(definition_unfolding,[],[f20,f42,f42])).
% 0.11/0.39  fof(f20,plain,(
% 0.11/0.39    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 0.11/0.39    inference(cnf_transformation,[],[f16])).
% 0.11/0.39  % SZS output end Proof for theBenchmark
% 0.11/0.39  % (11893)------------------------------
% 0.11/0.39  % (11893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.11/0.39  % (11893)Termination reason: Refutation
% 0.11/0.39  
% 0.11/0.39  % (11893)Memory used [KB]: 6268
% 0.11/0.39  % (11893)Time elapsed: 0.072 s
% 0.11/0.39  % (11893)------------------------------
% 0.11/0.39  % (11893)------------------------------
% 0.11/0.39  % (11884)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.11/0.39  % (11883)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.11/0.39  % (11879)Success in time 0.12 s
%------------------------------------------------------------------------------
