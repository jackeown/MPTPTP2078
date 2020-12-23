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
% DateTime   : Thu Dec  3 12:40:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 108 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 164 expanded)
%              Number of equality atoms :   30 (  77 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f56,f62,f65,f66,f74])).

fof(f74,plain,
    ( ~ spl2_2
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f69,f42,f46])).

fof(f46,plain,
    ( spl2_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f42,plain,
    ( spl2_1
  <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f69,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_1 ),
    inference(superposition,[],[f40,f43])).

fof(f43,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f40,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2)))) ) ),
    inference(definition_unfolding,[],[f26,f19,f31])).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f17,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f18,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f66,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f33,f46,f42])).

fof(f33,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f15,f19,f31])).

fof(f15,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f65,plain,
    ( spl2_2
    | spl2_4 ),
    inference(avatar_split_clause,[],[f63,f59,f46])).

fof(f59,plain,
    ( spl2_4
  <=> r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f63,plain,
    ( r2_hidden(sK1,sK0)
    | spl2_4 ),
    inference(resolution,[],[f61,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f31])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f61,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f62,plain,
    ( ~ spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f57,f53,f59])).

fof(f53,plain,
    ( spl2_3
  <=> r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f57,plain,
    ( ~ r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)
    | spl2_3 ),
    inference(resolution,[],[f55,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f55,plain,
    ( ~ r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f56,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f51,f42,f53])).

fof(f51,plain,
    ( ~ r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl2_1 ),
    inference(trivial_inequality_removal,[],[f50])).

fof(f50,plain,
    ( sK0 != sK0
    | ~ r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | spl2_1 ),
    inference(superposition,[],[f44,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f19])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f44,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f49,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f32,f46,f42])).

fof(f32,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f16,f19,f31])).

fof(f16,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:11:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (27605)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (27597)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (27589)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (27584)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (27605)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f49,f56,f62,f65,f66,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ~spl2_2 | ~spl2_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f69,f42,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    spl2_2 <=> r2_hidden(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    spl2_1 <=> sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ~r2_hidden(sK1,sK0) | ~spl2_1),
% 0.21/0.50    inference(superposition,[],[f40,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | ~spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f42])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))))) )),
% 0.21/0.50    inference(equality_resolution,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k3_enumset1(X2,X2,X2,X2,X2))))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f26,f19,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f17,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f18,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f24,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl2_1 | ~spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f46,f42])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ~r2_hidden(sK1,sK0) | sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 0.21/0.50    inference(definition_unfolding,[],[f15,f19,f31])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    spl2_2 | spl2_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f63,f59,f46])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    spl2_4 <=> r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    r2_hidden(sK1,sK0) | spl2_4),
% 0.21/0.50    inference(resolution,[],[f61,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f20,f31])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ~r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | spl2_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f59])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ~spl2_4 | spl2_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f57,f53,f59])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    spl2_3 <=> r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ~r1_xboole_0(k3_enumset1(sK1,sK1,sK1,sK1,sK1),sK0) | spl2_3),
% 0.21/0.50    inference(resolution,[],[f55,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ~r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl2_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f53])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ~spl2_3 | spl2_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f42,f53])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ~r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl2_1),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    sK0 != sK0 | ~r1_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | spl2_1),
% 0.21/0.50    inference(superposition,[],[f44,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f23,f19])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | spl2_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f42])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ~spl2_1 | spl2_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f46,f42])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    r2_hidden(sK1,sK0) | sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 0.21/0.50    inference(definition_unfolding,[],[f16,f19,f31])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (27605)------------------------------
% 0.21/0.50  % (27605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27605)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (27605)Memory used [KB]: 10746
% 0.21/0.50  % (27605)Time elapsed: 0.050 s
% 0.21/0.50  % (27605)------------------------------
% 0.21/0.50  % (27605)------------------------------
% 0.21/0.51  % (27582)Success in time 0.152 s
%------------------------------------------------------------------------------
