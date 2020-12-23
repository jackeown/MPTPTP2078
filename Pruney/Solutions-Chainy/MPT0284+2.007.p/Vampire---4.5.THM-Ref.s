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
% DateTime   : Thu Dec  3 12:41:39 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 124 expanded)
%              Number of leaves         :   13 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  163 ( 416 expanded)
%              Number of equality atoms :   17 (  52 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f152,f195])).

fof(f195,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f191,f114])).

fof(f114,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_2
  <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f191,plain,
    ( r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl4_2 ),
    inference(resolution,[],[f188,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f188,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k1_zfmisc_1(k4_xboole_0(sK1,sK0)))
    | spl4_2 ),
    inference(resolution,[],[f182,f54])).

fof(f54,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f182,plain,
    ( ~ r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k4_xboole_0(sK1,sK0))
    | spl4_2 ),
    inference(resolution,[],[f179,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f179,plain,
    ( ~ r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl4_2 ),
    inference(resolution,[],[f154,f53])).

fof(f53,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f154,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl4_2 ),
    inference(resolution,[],[f114,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f152,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f148,f110])).

fof(f110,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_1
  <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f148,plain,
    ( r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl4_1 ),
    inference(resolution,[],[f145,f37])).

fof(f145,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k1_zfmisc_1(k4_xboole_0(sK0,sK1)))
    | spl4_1 ),
    inference(resolution,[],[f140,f54])).

fof(f140,plain,
    ( ~ r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k4_xboole_0(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f138,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_tarski(k2_tarski(X1,X0)))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f51,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f32,f32])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f138,plain,
    ( ~ r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl4_1 ),
    inference(resolution,[],[f116,f53])).

fof(f116,plain,
    ( ~ r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | spl4_1 ),
    inference(resolution,[],[f110,f38])).

fof(f115,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f100,f112,f108])).

fof(f100,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(resolution,[],[f52,f47])).

fof(f47,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0)))),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(definition_unfolding,[],[f29,f32,f45])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k3_tarski(k2_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f34,f32])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f29,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f19])).

fof(f19,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f32])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:56:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (25252)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (25252)Refutation not found, incomplete strategy% (25252)------------------------------
% 0.21/0.51  % (25252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (25246)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (25252)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (25252)Memory used [KB]: 10618
% 0.21/0.52  % (25252)Time elapsed: 0.103 s
% 0.21/0.52  % (25252)------------------------------
% 0.21/0.52  % (25252)------------------------------
% 0.21/0.52  % (25244)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (25247)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (25272)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (25248)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (25268)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (25254)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (25249)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (25250)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (25270)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (25263)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.55  % (25259)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.55  % (25253)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.55  % (25262)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.55  % (25258)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.42/0.55  % (25273)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.55  % (25245)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.42/0.55  % (25247)Refutation found. Thanks to Tanya!
% 1.42/0.55  % SZS status Theorem for theBenchmark
% 1.42/0.55  % SZS output start Proof for theBenchmark
% 1.42/0.55  fof(f196,plain,(
% 1.42/0.55    $false),
% 1.42/0.55    inference(avatar_sat_refutation,[],[f115,f152,f195])).
% 1.42/0.55  fof(f195,plain,(
% 1.42/0.55    spl4_2),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f194])).
% 1.42/0.55  fof(f194,plain,(
% 1.42/0.55    $false | spl4_2),
% 1.42/0.55    inference(subsumption_resolution,[],[f191,f114])).
% 1.42/0.55  fof(f114,plain,(
% 1.42/0.55    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl4_2),
% 1.42/0.55    inference(avatar_component_clause,[],[f112])).
% 1.42/0.55  fof(f112,plain,(
% 1.42/0.55    spl4_2 <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.42/0.55  fof(f191,plain,(
% 1.42/0.55    r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl4_2),
% 1.42/0.55    inference(resolution,[],[f188,f37])).
% 1.42/0.55  fof(f37,plain,(
% 1.42/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f24])).
% 1.42/0.55  fof(f24,plain,(
% 1.42/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 1.42/0.55  fof(f23,plain,(
% 1.42/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f22,plain,(
% 1.42/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.42/0.55    inference(rectify,[],[f21])).
% 1.42/0.55  fof(f21,plain,(
% 1.42/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.42/0.55    inference(nnf_transformation,[],[f15])).
% 1.42/0.55  fof(f15,plain,(
% 1.42/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.42/0.55    inference(ennf_transformation,[],[f2])).
% 1.42/0.55  fof(f2,axiom,(
% 1.42/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.42/0.55  fof(f188,plain,(
% 1.42/0.55    ~r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k1_zfmisc_1(k4_xboole_0(sK1,sK0))) | spl4_2),
% 1.42/0.55    inference(resolution,[],[f182,f54])).
% 1.42/0.55  fof(f54,plain,(
% 1.42/0.55    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.42/0.55    inference(equality_resolution,[],[f39])).
% 1.42/0.55  fof(f39,plain,(
% 1.42/0.55    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.42/0.55    inference(cnf_transformation,[],[f28])).
% 1.42/0.55  fof(f28,plain,(
% 1.42/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 1.42/0.55  fof(f27,plain,(
% 1.42/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f26,plain,(
% 1.42/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.42/0.55    inference(rectify,[],[f25])).
% 1.42/0.55  fof(f25,plain,(
% 1.42/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.42/0.55    inference(nnf_transformation,[],[f9])).
% 1.42/0.55  fof(f9,axiom,(
% 1.42/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.42/0.55  fof(f182,plain,(
% 1.42/0.55    ~r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k4_xboole_0(sK1,sK0)) | spl4_2),
% 1.42/0.55    inference(resolution,[],[f179,f51])).
% 1.42/0.55  fof(f51,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f43,f32])).
% 1.42/0.55  fof(f32,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f10])).
% 1.42/0.55  fof(f10,axiom,(
% 1.42/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.42/0.55  fof(f43,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f16])).
% 1.42/0.55  fof(f16,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.42/0.55    inference(ennf_transformation,[],[f5])).
% 1.42/0.55  fof(f5,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.42/0.55  fof(f179,plain,(
% 1.42/0.55    ~r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl4_2),
% 1.42/0.55    inference(resolution,[],[f154,f53])).
% 1.42/0.55  fof(f53,plain,(
% 1.42/0.55    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.42/0.55    inference(equality_resolution,[],[f40])).
% 1.42/0.55  fof(f40,plain,(
% 1.42/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.42/0.55    inference(cnf_transformation,[],[f28])).
% 1.42/0.55  fof(f154,plain,(
% 1.42/0.55    ~r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl4_2),
% 1.42/0.55    inference(resolution,[],[f114,f38])).
% 1.42/0.55  fof(f38,plain,(
% 1.42/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f24])).
% 1.42/0.55  fof(f152,plain,(
% 1.42/0.55    spl4_1),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f151])).
% 1.42/0.55  fof(f151,plain,(
% 1.42/0.55    $false | spl4_1),
% 1.42/0.55    inference(subsumption_resolution,[],[f148,f110])).
% 1.42/0.55  fof(f110,plain,(
% 1.42/0.55    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl4_1),
% 1.42/0.55    inference(avatar_component_clause,[],[f108])).
% 1.42/0.55  fof(f108,plain,(
% 1.42/0.55    spl4_1 <=> r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 1.42/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.42/0.55  fof(f148,plain,(
% 1.42/0.55    r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl4_1),
% 1.42/0.55    inference(resolution,[],[f145,f37])).
% 1.42/0.55  fof(f145,plain,(
% 1.42/0.55    ~r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k1_zfmisc_1(k4_xboole_0(sK0,sK1))) | spl4_1),
% 1.42/0.55    inference(resolution,[],[f140,f54])).
% 1.42/0.55  fof(f140,plain,(
% 1.42/0.55    ~r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k4_xboole_0(sK0,sK1)) | spl4_1),
% 1.42/0.55    inference(resolution,[],[f138,f68])).
% 1.42/0.55  fof(f68,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_tarski(k2_tarski(X1,X0))) | ~r1_tarski(X2,X1)) )),
% 1.42/0.55    inference(superposition,[],[f51,f49])).
% 1.42/0.55  fof(f49,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 1.42/0.55    inference(definition_unfolding,[],[f31,f32,f32])).
% 1.42/0.55  fof(f31,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f1])).
% 1.42/0.55  fof(f1,axiom,(
% 1.42/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.42/0.55  fof(f138,plain,(
% 1.42/0.55    ~r1_tarski(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl4_1),
% 1.42/0.55    inference(resolution,[],[f116,f53])).
% 1.42/0.55  fof(f116,plain,(
% 1.42/0.55    ~r2_hidden(sK2(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | spl4_1),
% 1.42/0.55    inference(resolution,[],[f110,f38])).
% 1.42/0.55  fof(f115,plain,(
% 1.42/0.55    ~spl4_1 | ~spl4_2),
% 1.42/0.55    inference(avatar_split_clause,[],[f100,f112,f108])).
% 1.42/0.55  fof(f100,plain,(
% 1.42/0.55    ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK1,sK0)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 1.42/0.55    inference(resolution,[],[f52,f47])).
% 1.42/0.55  fof(f47,plain,(
% 1.42/0.55    ~r1_tarski(k3_tarski(k2_tarski(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0)))),k1_zfmisc_1(k3_tarski(k2_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 1.42/0.55    inference(definition_unfolding,[],[f29,f32,f45])).
% 1.42/0.55  fof(f45,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k3_tarski(k2_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 1.42/0.55    inference(definition_unfolding,[],[f34,f32])).
% 1.42/0.55  fof(f34,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f3])).
% 1.42/0.55  fof(f3,axiom,(
% 1.42/0.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.42/0.55  fof(f29,plain,(
% 1.42/0.55    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.42/0.55    inference(cnf_transformation,[],[f20])).
% 1.42/0.55  fof(f20,plain,(
% 1.42/0.55    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f19])).
% 1.42/0.55  fof(f19,plain,(
% 1.42/0.55    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  fof(f13,plain,(
% 1.42/0.55    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 1.42/0.55    inference(ennf_transformation,[],[f12])).
% 1.42/0.55  fof(f12,negated_conjecture,(
% 1.42/0.55    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 1.42/0.55    inference(negated_conjecture,[],[f11])).
% 1.42/0.55  fof(f11,conjecture,(
% 1.42/0.55    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).
% 1.42/0.55  fof(f52,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f44,f32])).
% 1.42/0.55  fof(f44,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f18])).
% 1.42/0.55  fof(f18,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.42/0.55    inference(flattening,[],[f17])).
% 1.42/0.55  fof(f17,plain,(
% 1.42/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.42/0.55    inference(ennf_transformation,[],[f8])).
% 1.42/0.55  fof(f8,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.42/0.55  % SZS output end Proof for theBenchmark
% 1.42/0.55  % (25247)------------------------------
% 1.42/0.55  % (25247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (25247)Termination reason: Refutation
% 1.42/0.55  
% 1.42/0.55  % (25247)Memory used [KB]: 10746
% 1.42/0.55  % (25247)Time elapsed: 0.117 s
% 1.42/0.55  % (25247)------------------------------
% 1.42/0.55  % (25247)------------------------------
% 1.42/0.55  % (25243)Success in time 0.189 s
%------------------------------------------------------------------------------
