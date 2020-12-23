%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:14 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 139 expanded)
%              Number of leaves         :   23 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :  213 ( 360 expanded)
%              Number of equality atoms :   32 (  59 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f73,f146,f161,f177])).

fof(f177,plain,
    ( spl7_1
    | ~ spl7_2
    | spl7_6 ),
    inference(avatar_split_clause,[],[f171,f159,f67,f63])).

fof(f63,plain,
    ( spl7_1
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f67,plain,
    ( spl7_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f159,plain,
    ( spl7_6
  <=> r2_hidden(sK3(sK2,sK0),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f171,plain,
    ( ~ r2_hidden(sK2,sK1)
    | r1_tarski(sK2,sK0)
    | spl7_6 ),
    inference(resolution,[],[f162,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f162,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK2,sK0),X0)
        | ~ r2_hidden(X0,sK1) )
    | spl7_6 ),
    inference(resolution,[],[f160,f59])).

fof(f59,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK4(X0,X1),X3) )
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( ( r2_hidden(sK5(X0,X1),X0)
              & r2_hidden(sK4(X0,X1),sK5(X0,X1)) )
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK6(X0,X5),X0)
                & r2_hidden(X5,sK6(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK4(X0,X1),X3) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK4(X0,X1),X4) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK4(X0,X1),X4) )
     => ( r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK6(X0,X5),X0)
        & r2_hidden(X5,sK6(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f160,plain,
    ( ~ r2_hidden(sK3(sK2,sK0),k3_tarski(sK1))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f159])).

fof(f161,plain,
    ( ~ spl7_6
    | spl7_1
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f147,f144,f63,f159])).

fof(f144,plain,
    ( spl7_5
  <=> r1_tarski(k3_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f147,plain,
    ( ~ r2_hidden(sK3(sK2,sK0),k3_tarski(sK1))
    | spl7_1
    | ~ spl7_5 ),
    inference(resolution,[],[f145,f78])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r2_hidden(sK3(sK2,sK0),X0) )
    | spl7_1 ),
    inference(resolution,[],[f76,f64])).

fof(f64,plain,
    ( ~ r1_tarski(sK2,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r2_hidden(sK3(X0,X1),X2) ) ),
    inference(resolution,[],[f40,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f145,plain,
    ( r1_tarski(k3_tarski(sK1),sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f144])).

fof(f146,plain,
    ( spl7_5
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f142,f71,f144])).

fof(f71,plain,
    ( spl7_3
  <=> r1_setfam_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f142,plain,
    ( r1_tarski(k3_tarski(sK1),sK0)
    | ~ spl7_3 ),
    inference(resolution,[],[f140,f72])).

fof(f72,plain,
    ( r1_setfam_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f140,plain,(
    ! [X6,X7] :
      ( ~ r1_setfam_1(X7,k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6))
      | r1_tarski(k3_tarski(X7),X6) ) ),
    inference(superposition,[],[f39,f133])).

fof(f133,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(superposition,[],[f58,f57])).

fof(f57,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f33,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f34,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f58,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f35,f54,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f52])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f52])).

fof(f37,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f73,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f56,f71])).

fof(f56,plain,(
    r1_setfam_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f30,f55])).

fof(f30,plain,(
    r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(sK2,sK0)
    & r2_hidden(sK2,sK1)
    & r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,X0)
            & r2_hidden(X2,X1) )
        & r1_setfam_1(X1,k1_tarski(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,sK0)
          & r2_hidden(X2,sK1) )
      & r1_setfam_1(sK1,k1_tarski(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,sK0)
        & r2_hidden(X2,sK1) )
   => ( ~ r1_tarski(sK2,sK0)
      & r2_hidden(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
      & r1_setfam_1(X1,k1_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X1,k1_tarski(X0))
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X1,k1_tarski(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

fof(f69,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f31,f67])).

fof(f31,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    ~ r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n025.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 12:12:20 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.46  % (12800)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.17/0.46  % (12778)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.17/0.46  % (12781)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.17/0.48  % (12786)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.17/0.48  % (12795)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.17/0.48  % (12792)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.17/0.48  % (12798)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.17/0.48  % (12787)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.17/0.48  % (12777)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.17/0.48  % (12775)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.17/0.48  % (12795)Refutation not found, incomplete strategy% (12795)------------------------------
% 0.17/0.48  % (12795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.48  % (12795)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.48  
% 0.17/0.48  % (12795)Memory used [KB]: 10618
% 0.17/0.48  % (12795)Time elapsed: 0.059 s
% 0.17/0.48  % (12795)------------------------------
% 0.17/0.48  % (12795)------------------------------
% 0.17/0.49  % (12776)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.17/0.49  % (12779)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.17/0.49  % (12790)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.17/0.50  % (12774)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.17/0.50  % (12773)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.17/0.50  % (12797)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.17/0.50  % (12785)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.17/0.50  % (12796)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.17/0.51  % (12775)Refutation not found, incomplete strategy% (12775)------------------------------
% 0.17/0.51  % (12775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.51  % (12775)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.51  
% 0.17/0.51  % (12775)Memory used [KB]: 10618
% 0.17/0.51  % (12775)Time elapsed: 0.126 s
% 0.17/0.51  % (12775)------------------------------
% 0.17/0.51  % (12775)------------------------------
% 0.17/0.51  % (12792)Refutation found. Thanks to Tanya!
% 0.17/0.51  % SZS status Theorem for theBenchmark
% 0.17/0.51  % SZS output start Proof for theBenchmark
% 0.17/0.51  fof(f178,plain,(
% 0.17/0.51    $false),
% 0.17/0.51    inference(avatar_sat_refutation,[],[f65,f69,f73,f146,f161,f177])).
% 0.17/0.51  fof(f177,plain,(
% 0.17/0.51    spl7_1 | ~spl7_2 | spl7_6),
% 0.17/0.51    inference(avatar_split_clause,[],[f171,f159,f67,f63])).
% 0.17/0.51  fof(f63,plain,(
% 0.17/0.51    spl7_1 <=> r1_tarski(sK2,sK0)),
% 0.17/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.17/0.51  fof(f67,plain,(
% 0.17/0.51    spl7_2 <=> r2_hidden(sK2,sK1)),
% 0.17/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.17/0.51  fof(f159,plain,(
% 0.17/0.51    spl7_6 <=> r2_hidden(sK3(sK2,sK0),k3_tarski(sK1))),
% 0.17/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.17/0.51  fof(f171,plain,(
% 0.17/0.51    ~r2_hidden(sK2,sK1) | r1_tarski(sK2,sK0) | spl7_6),
% 0.17/0.51    inference(resolution,[],[f162,f41])).
% 0.17/0.51  fof(f41,plain,(
% 0.17/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.17/0.51    inference(cnf_transformation,[],[f23])).
% 0.17/0.51  fof(f23,plain,(
% 0.17/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.17/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 0.17/0.51  fof(f22,plain,(
% 0.17/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.17/0.51    introduced(choice_axiom,[])).
% 0.17/0.51  fof(f21,plain,(
% 0.17/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.17/0.51    inference(rectify,[],[f20])).
% 0.17/0.51  fof(f20,plain,(
% 0.17/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.17/0.51    inference(nnf_transformation,[],[f16])).
% 0.17/0.51  fof(f16,plain,(
% 0.17/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.17/0.51    inference(ennf_transformation,[],[f1])).
% 0.17/0.51  fof(f1,axiom,(
% 0.17/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.17/0.51  fof(f162,plain,(
% 0.17/0.51    ( ! [X0] : (~r2_hidden(sK3(sK2,sK0),X0) | ~r2_hidden(X0,sK1)) ) | spl7_6),
% 0.17/0.51    inference(resolution,[],[f160,f59])).
% 0.17/0.51  fof(f59,plain,(
% 0.17/0.51    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 0.17/0.51    inference(equality_resolution,[],[f45])).
% 0.17/0.51  fof(f45,plain,(
% 0.17/0.51    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 0.17/0.51    inference(cnf_transformation,[],[f29])).
% 0.17/0.51  fof(f29,plain,(
% 0.17/0.51    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK4(X0,X1),X3)) | ~r2_hidden(sK4(X0,X1),X1)) & ((r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),sK5(X0,X1))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK6(X0,X5),X0) & r2_hidden(X5,sK6(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.17/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f28,f27,f26])).
% 0.17/0.51  fof(f26,plain,(
% 0.17/0.51    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK4(X0,X1),X3)) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK4(X0,X1),X4)) | r2_hidden(sK4(X0,X1),X1))))),
% 0.17/0.51    introduced(choice_axiom,[])).
% 0.17/0.51  fof(f27,plain,(
% 0.17/0.51    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK4(X0,X1),X4)) => (r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),sK5(X0,X1))))),
% 0.17/0.51    introduced(choice_axiom,[])).
% 0.17/0.51  fof(f28,plain,(
% 0.17/0.51    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK6(X0,X5),X0) & r2_hidden(X5,sK6(X0,X5))))),
% 0.17/0.51    introduced(choice_axiom,[])).
% 0.17/0.51  fof(f25,plain,(
% 0.17/0.51    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.17/0.51    inference(rectify,[],[f24])).
% 0.17/0.51  fof(f24,plain,(
% 0.17/0.51    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 0.17/0.51    inference(nnf_transformation,[],[f7])).
% 0.17/0.51  fof(f7,axiom,(
% 0.17/0.51    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 0.17/0.51  fof(f160,plain,(
% 0.17/0.51    ~r2_hidden(sK3(sK2,sK0),k3_tarski(sK1)) | spl7_6),
% 0.17/0.51    inference(avatar_component_clause,[],[f159])).
% 0.17/0.51  fof(f161,plain,(
% 0.17/0.51    ~spl7_6 | spl7_1 | ~spl7_5),
% 0.17/0.51    inference(avatar_split_clause,[],[f147,f144,f63,f159])).
% 0.17/0.51  fof(f144,plain,(
% 0.17/0.51    spl7_5 <=> r1_tarski(k3_tarski(sK1),sK0)),
% 0.17/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.17/0.51  fof(f147,plain,(
% 0.17/0.51    ~r2_hidden(sK3(sK2,sK0),k3_tarski(sK1)) | (spl7_1 | ~spl7_5)),
% 0.17/0.51    inference(resolution,[],[f145,f78])).
% 0.17/0.51  fof(f78,plain,(
% 0.17/0.51    ( ! [X0] : (~r1_tarski(X0,sK0) | ~r2_hidden(sK3(sK2,sK0),X0)) ) | spl7_1),
% 0.17/0.51    inference(resolution,[],[f76,f64])).
% 0.17/0.51  fof(f64,plain,(
% 0.17/0.51    ~r1_tarski(sK2,sK0) | spl7_1),
% 0.17/0.51    inference(avatar_component_clause,[],[f63])).
% 0.17/0.51  fof(f76,plain,(
% 0.17/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r2_hidden(sK3(X0,X1),X2)) )),
% 0.17/0.51    inference(resolution,[],[f40,f42])).
% 0.17/0.51  fof(f42,plain,(
% 0.17/0.51    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.17/0.51    inference(cnf_transformation,[],[f23])).
% 0.17/0.51  fof(f40,plain,(
% 0.17/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.17/0.51    inference(cnf_transformation,[],[f23])).
% 0.17/0.51  fof(f145,plain,(
% 0.17/0.51    r1_tarski(k3_tarski(sK1),sK0) | ~spl7_5),
% 0.17/0.51    inference(avatar_component_clause,[],[f144])).
% 0.17/0.51  fof(f146,plain,(
% 0.17/0.51    spl7_5 | ~spl7_3),
% 0.17/0.51    inference(avatar_split_clause,[],[f142,f71,f144])).
% 0.17/0.51  fof(f71,plain,(
% 0.17/0.51    spl7_3 <=> r1_setfam_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.17/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.17/0.51  fof(f142,plain,(
% 0.17/0.51    r1_tarski(k3_tarski(sK1),sK0) | ~spl7_3),
% 0.17/0.51    inference(resolution,[],[f140,f72])).
% 0.17/0.51  fof(f72,plain,(
% 0.17/0.51    r1_setfam_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl7_3),
% 0.17/0.51    inference(avatar_component_clause,[],[f71])).
% 0.17/0.51  fof(f140,plain,(
% 0.17/0.51    ( ! [X6,X7] : (~r1_setfam_1(X7,k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6)) | r1_tarski(k3_tarski(X7),X6)) )),
% 0.17/0.51    inference(superposition,[],[f39,f133])).
% 0.17/0.51  fof(f133,plain,(
% 0.17/0.51    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.17/0.51    inference(superposition,[],[f58,f57])).
% 0.17/0.51  fof(f57,plain,(
% 0.17/0.51    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.17/0.51    inference(definition_unfolding,[],[f33,f55])).
% 0.17/0.51  fof(f55,plain,(
% 0.17/0.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.17/0.51    inference(definition_unfolding,[],[f34,f52])).
% 0.17/0.51  fof(f52,plain,(
% 0.17/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.17/0.51    inference(definition_unfolding,[],[f38,f51])).
% 0.17/0.51  fof(f51,plain,(
% 0.17/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.17/0.51    inference(definition_unfolding,[],[f49,f50])).
% 0.17/0.51  fof(f50,plain,(
% 0.17/0.51    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.17/0.51    inference(cnf_transformation,[],[f6])).
% 0.17/0.51  fof(f6,axiom,(
% 0.17/0.51    ! [X0,X1,X2,X3,X4] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).
% 0.17/0.51  fof(f49,plain,(
% 0.17/0.51    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.17/0.51    inference(cnf_transformation,[],[f5])).
% 0.17/0.51  fof(f5,axiom,(
% 0.17/0.51    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).
% 0.17/0.51  fof(f38,plain,(
% 0.17/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.17/0.51    inference(cnf_transformation,[],[f4])).
% 0.17/0.51  fof(f4,axiom,(
% 0.17/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.17/0.51  fof(f34,plain,(
% 0.17/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.17/0.51    inference(cnf_transformation,[],[f3])).
% 0.17/0.51  fof(f3,axiom,(
% 0.17/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.17/0.51  fof(f33,plain,(
% 0.17/0.51    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.17/0.51    inference(cnf_transformation,[],[f9])).
% 0.17/0.51  fof(f9,axiom,(
% 0.17/0.51    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.17/0.51  fof(f58,plain,(
% 0.17/0.51    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = X0) )),
% 0.17/0.51    inference(definition_unfolding,[],[f35,f54,f53])).
% 0.17/0.51  fof(f53,plain,(
% 0.17/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.17/0.51    inference(definition_unfolding,[],[f36,f52])).
% 0.17/0.51  fof(f36,plain,(
% 0.17/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.17/0.51    inference(cnf_transformation,[],[f10])).
% 0.17/0.51  fof(f10,axiom,(
% 0.17/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.17/0.51  fof(f54,plain,(
% 0.17/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.17/0.51    inference(definition_unfolding,[],[f37,f52])).
% 0.17/0.51  fof(f37,plain,(
% 0.17/0.51    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.17/0.51    inference(cnf_transformation,[],[f8])).
% 0.17/0.51  fof(f8,axiom,(
% 0.17/0.51    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.17/0.51  fof(f35,plain,(
% 0.17/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.17/0.51    inference(cnf_transformation,[],[f2])).
% 0.17/0.51  fof(f2,axiom,(
% 0.17/0.51    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.17/0.51  fof(f39,plain,(
% 0.17/0.51    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1)) )),
% 0.17/0.51    inference(cnf_transformation,[],[f15])).
% 0.17/0.51  fof(f15,plain,(
% 0.17/0.51    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1))),
% 0.17/0.51    inference(ennf_transformation,[],[f11])).
% 0.17/0.51  fof(f11,axiom,(
% 0.17/0.51    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).
% 0.17/0.51  fof(f73,plain,(
% 0.17/0.51    spl7_3),
% 0.17/0.51    inference(avatar_split_clause,[],[f56,f71])).
% 0.17/0.51  fof(f56,plain,(
% 0.17/0.51    r1_setfam_1(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 0.17/0.51    inference(definition_unfolding,[],[f30,f55])).
% 0.17/0.51  fof(f30,plain,(
% 0.17/0.51    r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.17/0.51    inference(cnf_transformation,[],[f19])).
% 0.17/0.51  fof(f19,plain,(
% 0.17/0.51    (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.17/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18,f17])).
% 0.17/0.51  fof(f17,plain,(
% 0.17/0.51    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0))) => (? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0)))),
% 0.17/0.51    introduced(choice_axiom,[])).
% 0.17/0.51  fof(f18,plain,(
% 0.17/0.51    ? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) => (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1))),
% 0.17/0.51    introduced(choice_axiom,[])).
% 0.17/0.51  fof(f14,plain,(
% 0.17/0.51    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0)))),
% 0.17/0.51    inference(ennf_transformation,[],[f13])).
% 0.17/0.51  fof(f13,negated_conjecture,(
% 0.17/0.51    ~! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.17/0.51    inference(negated_conjecture,[],[f12])).
% 0.17/0.51  fof(f12,conjecture,(
% 0.17/0.51    ! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.17/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).
% 0.17/0.51  fof(f69,plain,(
% 0.17/0.51    spl7_2),
% 0.17/0.51    inference(avatar_split_clause,[],[f31,f67])).
% 0.17/0.51  fof(f31,plain,(
% 0.17/0.51    r2_hidden(sK2,sK1)),
% 0.17/0.51    inference(cnf_transformation,[],[f19])).
% 0.17/0.51  fof(f65,plain,(
% 0.17/0.51    ~spl7_1),
% 0.17/0.51    inference(avatar_split_clause,[],[f32,f63])).
% 0.17/0.51  fof(f32,plain,(
% 0.17/0.51    ~r1_tarski(sK2,sK0)),
% 0.17/0.51    inference(cnf_transformation,[],[f19])).
% 0.17/0.51  % SZS output end Proof for theBenchmark
% 0.17/0.51  % (12792)------------------------------
% 0.17/0.51  % (12792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.51  % (12792)Termination reason: Refutation
% 0.17/0.51  
% 0.17/0.51  % (12792)Memory used [KB]: 10874
% 0.17/0.51  % (12792)Time elapsed: 0.128 s
% 0.17/0.51  % (12792)------------------------------
% 0.17/0.51  % (12792)------------------------------
% 0.17/0.51  % (12799)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.17/0.51  % (12784)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.17/0.51  % (12772)Success in time 0.176 s
%------------------------------------------------------------------------------
