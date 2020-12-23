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
% DateTime   : Thu Dec  3 12:40:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 111 expanded)
%              Number of leaves         :   16 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :  133 ( 215 expanded)
%              Number of equality atoms :   25 (  63 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f48,f52,f66,f74,f79,f85,f90])).

fof(f90,plain,
    ( ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f88,f32])).

fof(f32,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f19,f31,f23,f31])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f22,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f88,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(resolution,[],[f84,f51])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f84,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_10
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f85,plain,
    ( spl2_10
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f80,f77,f63,f82])).

fof(f63,plain,
    ( spl2_6
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f77,plain,
    ( spl2_9
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f80,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(resolution,[],[f78,f65])).

fof(f65,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f79,plain,
    ( spl2_9
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f75,f72,f63,f77])).

fof(f72,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1) )
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(resolution,[],[f73,f65])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X2)
        | ~ r2_hidden(X1,X2)
        | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f37,f72])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f66,plain,
    ( spl2_6
    | spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f61,f46,f41,f63])).

fof(f41,plain,
    ( spl2_1
  <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f46,plain,
    ( spl2_2
  <=> ! [X1,X0] :
        ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f61,plain,
    ( r2_hidden(sK0,sK1)
    | spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f47,f43])).

fof(f43,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f52,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f36,f50])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f48,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f35,f46])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f44,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f33,f41])).

fof(f33,plain,(
    ~ r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f18,f31])).

fof(f18,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:14 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.22/0.43  % (28998)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.43  % (28998)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f91,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f44,f48,f52,f66,f74,f79,f85,f90])).
% 0.22/0.43  fof(f90,plain,(
% 0.22/0.43    ~spl2_3 | ~spl2_10),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f89])).
% 0.22/0.43  fof(f89,plain,(
% 0.22/0.43    $false | (~spl2_3 | ~spl2_10)),
% 0.22/0.43    inference(subsumption_resolution,[],[f88,f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))),
% 0.22/0.43    inference(definition_unfolding,[],[f19,f31,f23,f31])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f20,f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f22,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.43    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.43    inference(negated_conjecture,[],[f9])).
% 0.22/0.43  fof(f9,conjecture,(
% 0.22/0.43    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 0.22/0.43  fof(f88,plain,(
% 0.22/0.43    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | (~spl2_3 | ~spl2_10)),
% 0.22/0.43    inference(resolution,[],[f84,f51])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) ) | ~spl2_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f50])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    spl2_3 <=> ! [X1,X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.43  fof(f84,plain,(
% 0.22/0.43    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl2_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f82])).
% 0.22/0.43  fof(f82,plain,(
% 0.22/0.43    spl2_10 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.44  fof(f85,plain,(
% 0.22/0.44    spl2_10 | ~spl2_6 | ~spl2_9),
% 0.22/0.44    inference(avatar_split_clause,[],[f80,f77,f63,f82])).
% 0.22/0.44  fof(f63,plain,(
% 0.22/0.44    spl2_6 <=> r2_hidden(sK0,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    spl2_9 <=> ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | (~spl2_6 | ~spl2_9)),
% 0.22/0.44    inference(resolution,[],[f78,f65])).
% 0.22/0.44  fof(f65,plain,(
% 0.22/0.44    r2_hidden(sK0,sK1) | ~spl2_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f63])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1)) ) | ~spl2_9),
% 0.22/0.44    inference(avatar_component_clause,[],[f77])).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    spl2_9 | ~spl2_6 | ~spl2_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f75,f72,f63,f77])).
% 0.22/0.44  fof(f72,plain,(
% 0.22/0.44    spl2_8 <=> ! [X1,X0,X2] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.44  fof(f75,plain,(
% 0.22/0.44    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k2_enumset1(sK0,sK0,sK0,X0),sK1)) ) | (~spl2_6 | ~spl2_8)),
% 0.22/0.44    inference(resolution,[],[f73,f65])).
% 0.22/0.44  fof(f73,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)) ) | ~spl2_8),
% 0.22/0.44    inference(avatar_component_clause,[],[f72])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    spl2_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f37,f72])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f29,f30])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.44    inference(flattening,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.44    inference(nnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    spl2_6 | spl2_1 | ~spl2_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f61,f46,f41,f63])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    spl2_1 <=> r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    spl2_2 <=> ! [X1,X0] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    r2_hidden(sK0,sK1) | (spl2_1 | ~spl2_2)),
% 0.22/0.44    inference(resolution,[],[f47,f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | spl2_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f41])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) ) | ~spl2_2),
% 0.22/0.44    inference(avatar_component_clause,[],[f46])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    spl2_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f36,f50])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f25,f23])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    spl2_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f35,f46])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f24,f31])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    ~spl2_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f33,f41])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ~r1_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.22/0.44    inference(definition_unfolding,[],[f18,f31])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (28998)------------------------------
% 0.22/0.44  % (28998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (28998)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (28998)Memory used [KB]: 6140
% 0.22/0.44  % (28998)Time elapsed: 0.006 s
% 0.22/0.44  % (28998)------------------------------
% 0.22/0.44  % (28998)------------------------------
% 0.22/0.44  % (28990)Success in time 0.08 s
%------------------------------------------------------------------------------
