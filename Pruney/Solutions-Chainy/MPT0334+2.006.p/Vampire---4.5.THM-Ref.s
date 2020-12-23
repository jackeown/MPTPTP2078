%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  66 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  134 ( 164 expanded)
%              Number of equality atoms :   64 (  83 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f58,f94,f100,f106])).

fof(f106,plain,
    ( spl4_2
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl4_2
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f103,f51])).

fof(f51,plain,
    ( sK0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f103,plain,
    ( sK0 = sK1
    | ~ spl4_8 ),
    inference(resolution,[],[f99,f42])).

fof(f42,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f99,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_8
  <=> r2_hidden(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f100,plain,
    ( spl4_8
    | spl4_7 ),
    inference(avatar_split_clause,[],[f95,f91,f97])).

fof(f91,plain,
    ( spl4_7
  <=> r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f95,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | spl4_7 ),
    inference(resolution,[],[f93,f63])).

fof(f63,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,k1_tarski(X3))
      | r2_hidden(X3,X2) ) ),
    inference(trivial_inequality_removal,[],[f62])).

fof(f62,plain,(
    ! [X2,X3] :
      ( X2 != X2
      | r1_xboole_0(X2,k1_tarski(X3))
      | r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f29,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f93,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f94,plain,
    ( ~ spl4_7
    | spl4_3 ),
    inference(avatar_split_clause,[],[f89,f55,f91])).

fof(f55,plain,
    ( spl4_3
  <=> k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK2,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f89,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | spl4_3 ),
    inference(subsumption_resolution,[],[f84,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f84,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK2,k1_tarski(sK1)))
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | spl4_3 ),
    inference(superposition,[],[f57,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f57,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK2,k1_tarski(sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f58,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f53,f44,f55])).

fof(f44,plain,
    ( spl4_1
  <=> k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) = k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f53,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK2,k1_tarski(sK1)))
    | spl4_1 ),
    inference(backward_demodulation,[],[f46,f31])).

fof(f46,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f52,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
        & X0 != X1 )
   => ( k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).

fof(f47,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f25,f44])).

fof(f25,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (15867)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.46  % (15867)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f47,f52,f58,f94,f100,f106])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    spl4_2 | ~spl4_8),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f105])).
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    $false | (spl4_2 | ~spl4_8)),
% 0.21/0.46    inference(subsumption_resolution,[],[f103,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    sK0 != sK1 | spl4_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    spl4_2 <=> sK0 = sK1),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    sK0 = sK1 | ~spl4_8),
% 0.21/0.46    inference(resolution,[],[f99,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.46    inference(equality_resolution,[],[f32])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.46    inference(cnf_transformation,[],[f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.46    inference(rectify,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.46    inference(nnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    r2_hidden(sK0,k1_tarski(sK1)) | ~spl4_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f97])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    spl4_8 <=> r2_hidden(sK0,k1_tarski(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.46  fof(f100,plain,(
% 0.21/0.46    spl4_8 | spl4_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f95,f91,f97])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    spl4_7 <=> r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.46  fof(f95,plain,(
% 0.21/0.46    r2_hidden(sK0,k1_tarski(sK1)) | spl4_7),
% 0.21/0.46    inference(resolution,[],[f93,f63])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X2,X3] : (r1_xboole_0(X2,k1_tarski(X3)) | r2_hidden(X3,X2)) )),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f62])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    ( ! [X2,X3] : (X2 != X2 | r1_xboole_0(X2,k1_tarski(X3)) | r2_hidden(X3,X2)) )),
% 0.21/0.46    inference(superposition,[],[f29,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.46    inference(nnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 0.21/0.46    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | spl4_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f91])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    ~spl4_7 | spl4_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f89,f55,f91])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl4_3 <=> k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK2,k1_tarski(sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | spl4_3),
% 0.21/0.46    inference(subsumption_resolution,[],[f84,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK2,k1_tarski(sK1))) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | spl4_3),
% 0.21/0.46    inference(superposition,[],[f57,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK2,k1_tarski(sK1))) | spl4_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f55])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    ~spl4_3 | spl4_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f53,f44,f55])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    spl4_1 <=> k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) = k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK2,k1_tarski(sK1))) | spl4_1),
% 0.21/0.46    inference(backward_demodulation,[],[f46,f31])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) | spl4_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f44])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ~spl4_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f24,f49])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    sK0 != sK1),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) & sK0 != sK1),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) & X0 != X1) => (k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) & sK0 != sK1)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) & X0 != X1)),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 0.21/0.46    inference(negated_conjecture,[],[f11])).
% 0.21/0.46  fof(f11,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    ~spl4_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f44])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (15867)------------------------------
% 0.21/0.46  % (15867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (15867)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (15867)Memory used [KB]: 6268
% 0.21/0.46  % (15867)Time elapsed: 0.008 s
% 0.21/0.46  % (15867)------------------------------
% 0.21/0.46  % (15867)------------------------------
% 0.21/0.47  % (15840)Success in time 0.105 s
%------------------------------------------------------------------------------
