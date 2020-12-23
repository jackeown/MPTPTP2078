%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 378 expanded)
%              Number of leaves         :   17 ( 126 expanded)
%              Depth                    :   14
%              Number of atoms          :  218 ( 857 expanded)
%              Number of equality atoms :  119 ( 665 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f212,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f72,f79,f109,f156,f157,f160,f211])).

fof(f211,plain,
    ( ~ spl3_1
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_4
    | spl3_5 ),
    inference(subsumption_resolution,[],[f209,f78])).

fof(f78,plain,
    ( sK1 != sK2
    | spl3_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f209,plain,
    ( sK1 = sK2
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f70,f57])).

fof(f57,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_1
  <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f70,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_4
  <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f160,plain,
    ( spl3_1
    | spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f133,f88,f65,f56])).

fof(f65,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f88,plain,
    ( spl3_6
  <=> r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f133,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl3_6 ),
    inference(resolution,[],[f49,f89])).

fof(f89,plain,
    ( r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f33,f40,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f157,plain,
    ( spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f146,f69,f60])).

fof(f60,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f146,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f130,f51])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f130,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | k2_enumset1(sK0,sK0,sK0,sK0) = X0
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f49,f119])).

fof(f119,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f50,f44])).

fof(f44,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f21,f40,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f38])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

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

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f39])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f156,plain,
    ( spl3_1
    | spl3_4
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl3_1
    | spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f154,f139])).

% (26866)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f139,plain,
    ( k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_1
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f58,f134])).

fof(f134,plain,
    ( k1_xboole_0 = sK1
    | spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f133,f58])).

fof(f58,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f154,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_1
    | spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f149,f112])).

fof(f112,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(resolution,[],[f46,f51])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f29,f39])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f149,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | spl3_1
    | spl3_4
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f138,f147])).

fof(f147,plain,
    ( k1_xboole_0 = sK2
    | spl3_4 ),
    inference(subsumption_resolution,[],[f146,f71])).

fof(f71,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f138,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))
    | spl3_1
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f44,f134])).

fof(f109,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f107,f90])).

fof(f90,plain,
    ( ~ r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f107,plain,(
    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f45,f44])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f26,f39])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f79,plain,
    ( ~ spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f74,f56,f76])).

fof(f74,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f73])).

fof(f73,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f43])).

fof(f43,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f22,f40,f40])).

fof(f22,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f42,f69,f65])).

fof(f42,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f23,f40])).

fof(f23,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f63,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f41,f60,f56])).

fof(f41,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f24,f40])).

fof(f24,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:24:52 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.54  % (26849)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (26849)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (26850)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.56  % (26851)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (26865)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.56  % (26857)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (26857)Refutation not found, incomplete strategy% (26857)------------------------------
% 0.22/0.56  % (26857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f212,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f63,f72,f79,f109,f156,f157,f160,f211])).
% 0.22/0.57  fof(f211,plain,(
% 0.22/0.57    ~spl3_1 | ~spl3_4 | spl3_5),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f210])).
% 0.22/0.57  fof(f210,plain,(
% 0.22/0.57    $false | (~spl3_1 | ~spl3_4 | spl3_5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f209,f78])).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    sK1 != sK2 | spl3_5),
% 0.22/0.57    inference(avatar_component_clause,[],[f76])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    spl3_5 <=> sK1 = sK2),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.57  fof(f209,plain,(
% 0.22/0.57    sK1 = sK2 | (~spl3_1 | ~spl3_4)),
% 0.22/0.57    inference(forward_demodulation,[],[f70,f57])).
% 0.22/0.57  fof(f57,plain,(
% 0.22/0.57    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f56])).
% 0.22/0.57  fof(f56,plain,(
% 0.22/0.57    spl3_1 <=> sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f69])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    spl3_4 <=> sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.57  fof(f160,plain,(
% 0.22/0.57    spl3_1 | spl3_3 | ~spl3_6),
% 0.22/0.57    inference(avatar_split_clause,[],[f133,f88,f65,f56])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    spl3_3 <=> k1_xboole_0 = sK1),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.57  fof(f88,plain,(
% 0.22/0.57    spl3_6 <=> r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.57  fof(f133,plain,(
% 0.22/0.57    k1_xboole_0 = sK1 | sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl3_6),
% 0.22/0.57    inference(resolution,[],[f49,f89])).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl3_6),
% 0.22/0.57    inference(avatar_component_clause,[],[f88])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 0.22/0.57    inference(definition_unfolding,[],[f33,f40,f40])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f25,f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f28,f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.57    inference(flattening,[],[f19])).
% 0.22/0.57  fof(f19,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.57    inference(nnf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.57  fof(f157,plain,(
% 0.22/0.57    spl3_2 | spl3_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f146,f69,f60])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    spl3_2 <=> k1_xboole_0 = sK2),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.57  fof(f146,plain,(
% 0.22/0.57    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 = sK2),
% 0.22/0.57    inference(resolution,[],[f130,f51])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.57    inference(flattening,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.57    inference(nnf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.57  fof(f130,plain,(
% 0.22/0.57    ( ! [X0] : (~r1_tarski(X0,sK2) | k2_enumset1(sK0,sK0,sK0,sK0) = X0 | k1_xboole_0 = X0) )),
% 0.22/0.57    inference(resolution,[],[f49,f119])).
% 0.22/0.57  fof(f119,plain,(
% 0.22/0.57    ( ! [X0] : (r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r1_tarski(X0,sK2)) )),
% 0.22/0.57    inference(superposition,[],[f50,f44])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 0.22/0.57    inference(definition_unfolding,[],[f21,f40,f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f27,f38])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f9])).
% 0.22/0.57  fof(f9,axiom,(
% 0.22/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.57    inference(ennf_transformation,[],[f11])).
% 0.22/0.57  fof(f11,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.57    inference(negated_conjecture,[],[f10])).
% 0.22/0.57  fof(f10,conjecture,(
% 0.22/0.57    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(definition_unfolding,[],[f37,f39])).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f2])).
% 0.22/0.57  fof(f2,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.22/0.57  fof(f156,plain,(
% 0.22/0.57    spl3_1 | spl3_4 | ~spl3_6),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f155])).
% 0.22/0.57  fof(f155,plain,(
% 0.22/0.57    $false | (spl3_1 | spl3_4 | ~spl3_6)),
% 0.22/0.57    inference(subsumption_resolution,[],[f154,f139])).
% 0.22/0.57  % (26866)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.57  fof(f139,plain,(
% 0.22/0.57    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) | (spl3_1 | ~spl3_6)),
% 0.22/0.57    inference(backward_demodulation,[],[f58,f134])).
% 0.22/0.57  fof(f134,plain,(
% 0.22/0.57    k1_xboole_0 = sK1 | (spl3_1 | ~spl3_6)),
% 0.22/0.57    inference(subsumption_resolution,[],[f133,f58])).
% 0.22/0.57  fof(f58,plain,(
% 0.22/0.57    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | spl3_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f56])).
% 0.22/0.57  fof(f154,plain,(
% 0.22/0.57    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | (spl3_1 | spl3_4 | ~spl3_6)),
% 0.22/0.57    inference(forward_demodulation,[],[f149,f112])).
% 0.22/0.57  fof(f112,plain,(
% 0.22/0.57    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.22/0.57    inference(resolution,[],[f46,f51])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1) )),
% 0.22/0.57    inference(definition_unfolding,[],[f29,f39])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.57    inference(ennf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.57  fof(f149,plain,(
% 0.22/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) | (spl3_1 | spl3_4 | ~spl3_6)),
% 0.22/0.57    inference(backward_demodulation,[],[f138,f147])).
% 0.22/0.57  fof(f147,plain,(
% 0.22/0.57    k1_xboole_0 = sK2 | spl3_4),
% 0.22/0.57    inference(subsumption_resolution,[],[f146,f71])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | spl3_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f69])).
% 0.22/0.57  fof(f138,plain,(
% 0.22/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) | (spl3_1 | ~spl3_6)),
% 0.22/0.57    inference(backward_demodulation,[],[f44,f134])).
% 0.22/0.57  fof(f109,plain,(
% 0.22/0.57    spl3_6),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f108])).
% 0.22/0.57  fof(f108,plain,(
% 0.22/0.57    $false | spl3_6),
% 0.22/0.57    inference(subsumption_resolution,[],[f107,f90])).
% 0.22/0.57  fof(f90,plain,(
% 0.22/0.57    ~r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | spl3_6),
% 0.22/0.57    inference(avatar_component_clause,[],[f88])).
% 0.22/0.57  fof(f107,plain,(
% 0.22/0.57    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.22/0.57    inference(superposition,[],[f45,f44])).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.22/0.57    inference(definition_unfolding,[],[f26,f39])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    ~spl3_5 | ~spl3_1),
% 0.22/0.57    inference(avatar_split_clause,[],[f74,f56,f76])).
% 0.22/0.57  fof(f74,plain,(
% 0.22/0.57    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != sK2),
% 0.22/0.57    inference(inner_rewriting,[],[f73])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != sK2),
% 0.22/0.57    inference(inner_rewriting,[],[f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.57    inference(definition_unfolding,[],[f22,f40,f40])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f72,plain,(
% 0.22/0.57    ~spl3_3 | ~spl3_4),
% 0.22/0.57    inference(avatar_split_clause,[],[f42,f69,f65])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 0.22/0.57    inference(definition_unfolding,[],[f23,f40])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    ~spl3_1 | ~spl3_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f41,f60,f56])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    k1_xboole_0 != sK2 | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.22/0.57    inference(definition_unfolding,[],[f24,f40])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (26849)------------------------------
% 0.22/0.57  % (26849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (26849)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (26849)Memory used [KB]: 10746
% 0.22/0.57  % (26849)Time elapsed: 0.130 s
% 0.22/0.57  % (26849)------------------------------
% 0.22/0.57  % (26849)------------------------------
% 0.22/0.57  % (26859)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.57  % (26858)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.57  % (26842)Success in time 0.202 s
%------------------------------------------------------------------------------
