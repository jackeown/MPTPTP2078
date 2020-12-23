%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:49 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   48 (  57 expanded)
%              Number of leaves         :   12 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 111 expanded)
%              Number of equality atoms :   36 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32503)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f92,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f82,f88,f91])).

fof(f91,plain,(
    ~ spl1_6 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f38,f87,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f87,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl1_6
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f38,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f88,plain,
    ( spl1_6
    | spl1_5 ),
    inference(avatar_split_clause,[],[f83,f79,f85])).

fof(f79,plain,
    ( spl1_5
  <=> r1_xboole_0(sK0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f83,plain,
    ( r2_hidden(sK0,sK0)
    | spl1_5 ),
    inference(resolution,[],[f81,f59])).

fof(f59,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,k1_tarski(X3))
      | r2_hidden(X3,X2) ) ),
    inference(trivial_inequality_removal,[],[f58])).

fof(f58,plain,(
    ! [X2,X3] :
      ( X2 != X2
      | r1_xboole_0(X2,k1_tarski(X3))
      | r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f35,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f21])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f81,plain,
    ( ~ r1_xboole_0(sK0,k1_tarski(sK0))
    | spl1_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f82,plain,
    ( ~ spl1_5
    | spl1_1 ),
    inference(avatar_split_clause,[],[f77,f41,f79])).

fof(f41,plain,
    ( spl1_1
  <=> sK0 = k6_subset_1(k2_xboole_0(sK0,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f77,plain,
    ( ~ r1_xboole_0(sK0,k1_tarski(sK0))
    | spl1_1 ),
    inference(trivial_inequality_removal,[],[f72])).

fof(f72,plain,
    ( sK0 != sK0
    | ~ r1_xboole_0(sK0,k1_tarski(sK0))
    | spl1_1 ),
    inference(superposition,[],[f43,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f21])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f43,plain,
    ( sK0 != k6_subset_1(k2_xboole_0(sK0,k1_tarski(sK0)),k1_tarski(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f44,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f32,f41])).

fof(f32,plain,(
    sK0 != k6_subset_1(k2_xboole_0(sK0,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f24,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f20,plain,(
    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f14])).

fof(f14,plain,
    ( ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0
   => sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:46:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (32512)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (32520)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.23/0.52  % (32520)Refutation found. Thanks to Tanya!
% 1.23/0.52  % SZS status Theorem for theBenchmark
% 1.23/0.52  % (32504)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.23/0.52  % SZS output start Proof for theBenchmark
% 1.23/0.52  % (32503)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.52  fof(f92,plain,(
% 1.23/0.52    $false),
% 1.23/0.52    inference(avatar_sat_refutation,[],[f44,f82,f88,f91])).
% 1.23/0.52  fof(f91,plain,(
% 1.23/0.52    ~spl1_6),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f89])).
% 1.23/0.52  fof(f89,plain,(
% 1.23/0.52    $false | ~spl1_6),
% 1.23/0.52    inference(unit_resulting_resolution,[],[f38,f87,f28])).
% 1.23/0.52  fof(f28,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f13])).
% 1.23/0.52  fof(f13,plain,(
% 1.23/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.23/0.52    inference(ennf_transformation,[],[f8])).
% 1.23/0.52  fof(f8,axiom,(
% 1.23/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.23/0.52  fof(f87,plain,(
% 1.23/0.52    r2_hidden(sK0,sK0) | ~spl1_6),
% 1.23/0.52    inference(avatar_component_clause,[],[f85])).
% 1.23/0.52  fof(f85,plain,(
% 1.23/0.52    spl1_6 <=> r2_hidden(sK0,sK0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 1.23/0.52  fof(f38,plain,(
% 1.23/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.23/0.52    inference(equality_resolution,[],[f30])).
% 1.23/0.52  fof(f30,plain,(
% 1.23/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  fof(f19,plain,(
% 1.23/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.23/0.52    inference(flattening,[],[f18])).
% 1.23/0.52  fof(f18,plain,(
% 1.23/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.23/0.52    inference(nnf_transformation,[],[f1])).
% 1.23/0.52  fof(f1,axiom,(
% 1.23/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.23/0.52  fof(f88,plain,(
% 1.23/0.52    spl1_6 | spl1_5),
% 1.23/0.52    inference(avatar_split_clause,[],[f83,f79,f85])).
% 1.23/0.52  fof(f79,plain,(
% 1.23/0.52    spl1_5 <=> r1_xboole_0(sK0,k1_tarski(sK0))),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 1.23/0.52  fof(f83,plain,(
% 1.23/0.52    r2_hidden(sK0,sK0) | spl1_5),
% 1.23/0.52    inference(resolution,[],[f81,f59])).
% 1.23/0.52  fof(f59,plain,(
% 1.23/0.52    ( ! [X2,X3] : (r1_xboole_0(X2,k1_tarski(X3)) | r2_hidden(X3,X2)) )),
% 1.23/0.52    inference(trivial_inequality_removal,[],[f58])).
% 1.23/0.52  fof(f58,plain,(
% 1.23/0.52    ( ! [X2,X3] : (X2 != X2 | r1_xboole_0(X2,k1_tarski(X3)) | r2_hidden(X3,X2)) )),
% 1.23/0.52    inference(superposition,[],[f35,f33])).
% 1.23/0.52  fof(f33,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k6_subset_1(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.23/0.52    inference(definition_unfolding,[],[f23,f21])).
% 1.23/0.52  fof(f21,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f6])).
% 1.23/0.52  fof(f6,axiom,(
% 1.23/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.23/0.52  fof(f23,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f16])).
% 1.23/0.52  fof(f16,plain,(
% 1.23/0.52    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.23/0.52    inference(nnf_transformation,[],[f5])).
% 1.23/0.52  fof(f5,axiom,(
% 1.23/0.52    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.23/0.52  fof(f35,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k6_subset_1(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.23/0.52    inference(definition_unfolding,[],[f26,f21])).
% 1.23/0.52  fof(f26,plain,(
% 1.23/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.23/0.52    inference(cnf_transformation,[],[f17])).
% 1.23/0.52  fof(f17,plain,(
% 1.23/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.23/0.52    inference(nnf_transformation,[],[f2])).
% 1.23/0.52  fof(f2,axiom,(
% 1.23/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.23/0.52  fof(f81,plain,(
% 1.23/0.52    ~r1_xboole_0(sK0,k1_tarski(sK0)) | spl1_5),
% 1.23/0.52    inference(avatar_component_clause,[],[f79])).
% 1.23/0.52  fof(f82,plain,(
% 1.23/0.52    ~spl1_5 | spl1_1),
% 1.23/0.52    inference(avatar_split_clause,[],[f77,f41,f79])).
% 1.23/0.52  fof(f41,plain,(
% 1.23/0.52    spl1_1 <=> sK0 = k6_subset_1(k2_xboole_0(sK0,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.23/0.52  fof(f77,plain,(
% 1.23/0.52    ~r1_xboole_0(sK0,k1_tarski(sK0)) | spl1_1),
% 1.23/0.52    inference(trivial_inequality_removal,[],[f72])).
% 1.23/0.52  fof(f72,plain,(
% 1.23/0.52    sK0 != sK0 | ~r1_xboole_0(sK0,k1_tarski(sK0)) | spl1_1),
% 1.23/0.52    inference(superposition,[],[f43,f37])).
% 1.23/0.52  fof(f37,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k6_subset_1(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.23/0.52    inference(definition_unfolding,[],[f27,f21])).
% 1.23/0.52  fof(f27,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f12])).
% 1.23/0.52  fof(f12,plain,(
% 1.23/0.52    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.23/0.52    inference(ennf_transformation,[],[f3])).
% 1.23/0.52  fof(f3,axiom,(
% 1.23/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 1.23/0.52  fof(f43,plain,(
% 1.23/0.52    sK0 != k6_subset_1(k2_xboole_0(sK0,k1_tarski(sK0)),k1_tarski(sK0)) | spl1_1),
% 1.23/0.52    inference(avatar_component_clause,[],[f41])).
% 1.23/0.52  fof(f44,plain,(
% 1.23/0.52    ~spl1_1),
% 1.23/0.52    inference(avatar_split_clause,[],[f32,f41])).
% 1.23/0.52  fof(f32,plain,(
% 1.23/0.52    sK0 != k6_subset_1(k2_xboole_0(sK0,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.23/0.52    inference(definition_unfolding,[],[f20,f24])).
% 1.23/0.52  fof(f24,plain,(
% 1.23/0.52    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.23/0.52    inference(cnf_transformation,[],[f7])).
% 1.23/0.52  fof(f7,axiom,(
% 1.23/0.52    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.23/0.52  fof(f20,plain,(
% 1.23/0.52    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0))),
% 1.23/0.52    inference(cnf_transformation,[],[f15])).
% 1.23/0.52  fof(f15,plain,(
% 1.23/0.52    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0))),
% 1.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f14])).
% 1.23/0.52  fof(f14,plain,(
% 1.23/0.52    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0 => sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f11,plain,(
% 1.23/0.52    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0),
% 1.23/0.52    inference(ennf_transformation,[],[f10])).
% 1.23/0.52  fof(f10,negated_conjecture,(
% 1.23/0.52    ~! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0),
% 1.23/0.52    inference(negated_conjecture,[],[f9])).
% 1.23/0.52  fof(f9,conjecture,(
% 1.23/0.52    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).
% 1.23/0.52  % SZS output end Proof for theBenchmark
% 1.23/0.52  % (32520)------------------------------
% 1.23/0.52  % (32520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (32520)Termination reason: Refutation
% 1.23/0.52  
% 1.23/0.52  % (32520)Memory used [KB]: 10746
% 1.23/0.52  % (32520)Time elapsed: 0.068 s
% 1.23/0.52  % (32520)------------------------------
% 1.23/0.52  % (32520)------------------------------
% 1.23/0.52  % (32496)Success in time 0.158 s
%------------------------------------------------------------------------------
