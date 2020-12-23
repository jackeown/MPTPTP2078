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
% DateTime   : Thu Dec  3 12:46:11 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 111 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  118 ( 171 expanded)
%              Number of equality atoms :   54 (  97 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f67,f84])).

fof(f84,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_1 ),
    inference(superposition,[],[f76,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f76,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f72,f48])).

fof(f48,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f35,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f72,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))
    | ~ spl3_1 ),
    inference(superposition,[],[f52,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k2_enumset1(sK2(k1_xboole_0),sK2(k1_xboole_0),sK2(k1_xboole_0),sK2(k1_xboole_0))
    | ~ spl3_1 ),
    inference(superposition,[],[f68,f32])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f68,plain,
    ( k1_xboole_0 = k2_xboole_0(k2_enumset1(sK2(k1_xboole_0),sK2(k1_xboole_0),sK2(k1_xboole_0),sK2(k1_xboole_0)),k1_xboole_0)
    | ~ spl3_1 ),
    inference(resolution,[],[f56,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = X1 ) ),
    inference(definition_unfolding,[],[f39,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f44])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f56,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl3_1
  <=> r2_hidden(sK2(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f52,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f41,f47,f46,f47,f47])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f45])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f67,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f66,f58,f55])).

fof(f58,plain,
    ( spl3_2
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f66,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(sK2(k1_xboole_0),k1_xboole_0) ) ),
    inference(resolution,[],[f29,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(sK2(X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(sK2(X1),X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f26])).

fof(f26,plain,(
    ! [X1] :
      ( ? [X3] : r2_hidden(X3,X1)
     => r2_hidden(sK2(X1),X1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] : r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] : ~ r2_hidden(X3,X1)
            & r2_hidden(X2,X0) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f29,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 != sK0
    & r1_setfam_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK0
      & r1_setfam_1(sK0,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f65,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f62])).

fof(f62,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f30,f61])).

fof(f61,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_2 ),
    inference(resolution,[],[f59,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f59,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.52  % (19852)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.28/0.53  % (19860)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.28/0.53  % (19860)Refutation not found, incomplete strategy% (19860)------------------------------
% 1.28/0.53  % (19860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (19860)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (19860)Memory used [KB]: 1663
% 1.28/0.53  % (19860)Time elapsed: 0.115 s
% 1.28/0.53  % (19860)------------------------------
% 1.28/0.53  % (19860)------------------------------
% 1.28/0.53  % (19841)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.53  % (19841)Refutation found. Thanks to Tanya!
% 1.28/0.53  % SZS status Theorem for theBenchmark
% 1.28/0.53  % SZS output start Proof for theBenchmark
% 1.28/0.53  fof(f85,plain,(
% 1.28/0.53    $false),
% 1.28/0.53    inference(avatar_sat_refutation,[],[f65,f67,f84])).
% 1.28/0.53  fof(f84,plain,(
% 1.28/0.53    ~spl3_1),
% 1.28/0.53    inference(avatar_contradiction_clause,[],[f83])).
% 1.28/0.53  fof(f83,plain,(
% 1.28/0.53    $false | ~spl3_1),
% 1.28/0.53    inference(trivial_inequality_removal,[],[f82])).
% 1.28/0.53  fof(f82,plain,(
% 1.28/0.53    k1_xboole_0 != k1_xboole_0 | ~spl3_1),
% 1.28/0.53    inference(superposition,[],[f76,f31])).
% 1.28/0.53  fof(f31,plain,(
% 1.28/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f5])).
% 1.28/0.53  fof(f5,axiom,(
% 1.28/0.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.28/0.53  fof(f76,plain,(
% 1.28/0.53    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_1),
% 1.28/0.53    inference(forward_demodulation,[],[f72,f48])).
% 1.28/0.53  fof(f48,plain,(
% 1.28/0.53    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.28/0.53    inference(definition_unfolding,[],[f35,f45])).
% 1.28/0.53  fof(f45,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.28/0.53    inference(definition_unfolding,[],[f36,f44])).
% 1.28/0.53  fof(f44,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f37,f43])).
% 1.28/0.53  fof(f43,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f8])).
% 1.28/0.53  fof(f8,axiom,(
% 1.28/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.28/0.53  fof(f37,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f7])).
% 1.28/0.53  fof(f7,axiom,(
% 1.28/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.28/0.53  fof(f36,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f12])).
% 1.28/0.53  fof(f12,axiom,(
% 1.28/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.28/0.53  fof(f35,plain,(
% 1.28/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.28/0.53    inference(cnf_transformation,[],[f15])).
% 1.28/0.53  fof(f15,plain,(
% 1.28/0.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.28/0.53    inference(rectify,[],[f1])).
% 1.28/0.53  fof(f1,axiom,(
% 1.28/0.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.28/0.53  fof(f72,plain,(
% 1.28/0.53    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) | ~spl3_1),
% 1.28/0.53    inference(superposition,[],[f52,f69])).
% 1.28/0.53  fof(f69,plain,(
% 1.28/0.53    k1_xboole_0 = k2_enumset1(sK2(k1_xboole_0),sK2(k1_xboole_0),sK2(k1_xboole_0),sK2(k1_xboole_0)) | ~spl3_1),
% 1.28/0.53    inference(superposition,[],[f68,f32])).
% 1.28/0.53  fof(f32,plain,(
% 1.28/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.28/0.53    inference(cnf_transformation,[],[f4])).
% 1.28/0.53  fof(f4,axiom,(
% 1.28/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.28/0.53  fof(f68,plain,(
% 1.28/0.53    k1_xboole_0 = k2_xboole_0(k2_enumset1(sK2(k1_xboole_0),sK2(k1_xboole_0),sK2(k1_xboole_0),sK2(k1_xboole_0)),k1_xboole_0) | ~spl3_1),
% 1.28/0.53    inference(resolution,[],[f56,f49])).
% 1.28/0.53  fof(f49,plain,(
% 1.28/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = X1) )),
% 1.28/0.53    inference(definition_unfolding,[],[f39,f47])).
% 1.28/0.53  fof(f47,plain,(
% 1.28/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.28/0.53    inference(definition_unfolding,[],[f33,f44])).
% 1.28/0.53  fof(f33,plain,(
% 1.28/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f6])).
% 1.28/0.53  fof(f6,axiom,(
% 1.28/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.28/0.53  fof(f39,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f20])).
% 1.28/0.53  fof(f20,plain,(
% 1.28/0.53    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 1.28/0.53    inference(ennf_transformation,[],[f9])).
% 1.28/0.53  fof(f9,axiom,(
% 1.28/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 1.28/0.53  fof(f56,plain,(
% 1.28/0.53    r2_hidden(sK2(k1_xboole_0),k1_xboole_0) | ~spl3_1),
% 1.28/0.53    inference(avatar_component_clause,[],[f55])).
% 1.28/0.53  fof(f55,plain,(
% 1.28/0.53    spl3_1 <=> r2_hidden(sK2(k1_xboole_0),k1_xboole_0)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.28/0.53  fof(f52,plain,(
% 1.28/0.53    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))))) )),
% 1.28/0.53    inference(equality_resolution,[],[f51])).
% 1.28/0.53  fof(f51,plain,(
% 1.28/0.53    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))))) )),
% 1.28/0.53    inference(definition_unfolding,[],[f41,f47,f46,f47,f47])).
% 1.28/0.53  fof(f46,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.28/0.53    inference(definition_unfolding,[],[f38,f45])).
% 1.28/0.53  fof(f38,plain,(
% 1.28/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f3])).
% 1.28/0.53  fof(f3,axiom,(
% 1.28/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.28/0.53  fof(f41,plain,(
% 1.28/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f28])).
% 1.28/0.53  fof(f28,plain,(
% 1.28/0.53    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 1.28/0.53    inference(nnf_transformation,[],[f10])).
% 1.28/0.53  fof(f10,axiom,(
% 1.28/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 1.28/0.53  fof(f67,plain,(
% 1.28/0.53    spl3_1 | spl3_2),
% 1.28/0.53    inference(avatar_split_clause,[],[f66,f58,f55])).
% 1.28/0.53  fof(f58,plain,(
% 1.28/0.53    spl3_2 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 1.28/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.28/0.53  fof(f66,plain,(
% 1.28/0.53    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(sK2(k1_xboole_0),k1_xboole_0)) )),
% 1.28/0.53    inference(resolution,[],[f29,f40])).
% 1.28/0.53  fof(f40,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(sK2(X1),X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f27])).
% 1.28/0.53  fof(f27,plain,(
% 1.28/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f26])).
% 1.28/0.53  fof(f26,plain,(
% 1.28/0.53    ! [X1] : (? [X3] : r2_hidden(X3,X1) => r2_hidden(sK2(X1),X1))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f21,plain,(
% 1.28/0.53    ! [X0,X1] : (! [X2] : (? [X3] : r2_hidden(X3,X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 1.28/0.53    inference(ennf_transformation,[],[f17])).
% 1.28/0.53  fof(f17,plain,(
% 1.28/0.53    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~r2_hidden(X3,X1) & r2_hidden(X2,X0)))),
% 1.28/0.53    inference(pure_predicate_removal,[],[f16])).
% 1.28/0.53  fof(f16,plain,(
% 1.28/0.53    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 1.28/0.53    inference(unused_predicate_definition_removal,[],[f11])).
% 1.28/0.53  fof(f11,axiom,(
% 1.28/0.53    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 1.28/0.53  fof(f29,plain,(
% 1.28/0.53    r1_setfam_1(sK0,k1_xboole_0)),
% 1.28/0.53    inference(cnf_transformation,[],[f23])).
% 1.28/0.53  fof(f23,plain,(
% 1.28/0.53    k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0)),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f22])).
% 1.28/0.53  fof(f22,plain,(
% 1.28/0.53    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0)) => (k1_xboole_0 != sK0 & r1_setfam_1(sK0,k1_xboole_0))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f18,plain,(
% 1.28/0.53    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 1.28/0.53    inference(ennf_transformation,[],[f14])).
% 1.28/0.53  fof(f14,negated_conjecture,(
% 1.28/0.53    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.28/0.53    inference(negated_conjecture,[],[f13])).
% 1.28/0.53  fof(f13,conjecture,(
% 1.28/0.53    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).
% 1.28/0.53  fof(f65,plain,(
% 1.28/0.53    ~spl3_2),
% 1.28/0.53    inference(avatar_contradiction_clause,[],[f62])).
% 1.28/0.53  fof(f62,plain,(
% 1.28/0.53    $false | ~spl3_2),
% 1.28/0.53    inference(subsumption_resolution,[],[f30,f61])).
% 1.28/0.53  fof(f61,plain,(
% 1.28/0.53    k1_xboole_0 = sK0 | ~spl3_2),
% 1.28/0.53    inference(resolution,[],[f59,f34])).
% 1.28/0.53  fof(f34,plain,(
% 1.28/0.53    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 1.28/0.53    inference(cnf_transformation,[],[f25])).
% 1.28/0.53  fof(f25,plain,(
% 1.28/0.53    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f24])).
% 1.28/0.53  fof(f24,plain,(
% 1.28/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f19,plain,(
% 1.28/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.28/0.53    inference(ennf_transformation,[],[f2])).
% 1.28/0.53  fof(f2,axiom,(
% 1.28/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.28/0.53  fof(f59,plain,(
% 1.28/0.53    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl3_2),
% 1.28/0.53    inference(avatar_component_clause,[],[f58])).
% 1.28/0.53  fof(f30,plain,(
% 1.28/0.53    k1_xboole_0 != sK0),
% 1.28/0.53    inference(cnf_transformation,[],[f23])).
% 1.28/0.53  % SZS output end Proof for theBenchmark
% 1.28/0.53  % (19841)------------------------------
% 1.28/0.53  % (19841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (19841)Termination reason: Refutation
% 1.28/0.53  
% 1.28/0.53  % (19841)Memory used [KB]: 10746
% 1.28/0.53  % (19841)Time elapsed: 0.126 s
% 1.28/0.53  % (19841)------------------------------
% 1.28/0.53  % (19841)------------------------------
% 1.28/0.54  % (19840)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.54  % (19868)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.28/0.54  % (19851)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.28/0.54  % (19850)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.28/0.54  % (19850)Refutation not found, incomplete strategy% (19850)------------------------------
% 1.28/0.54  % (19850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (19850)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (19850)Memory used [KB]: 10618
% 1.28/0.54  % (19850)Time elapsed: 0.131 s
% 1.28/0.54  % (19850)------------------------------
% 1.28/0.54  % (19850)------------------------------
% 1.28/0.54  % (19853)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.46/0.54  % (19838)Success in time 0.189 s
%------------------------------------------------------------------------------
