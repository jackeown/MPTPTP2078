%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0543+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:09 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 247 expanded)
%              Number of leaves         :   19 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  422 (1227 expanded)
%              Number of equality atoms :   33 ( 152 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f98,f169,f179,f505,f1219,f1253,f1273,f1277])).

fof(f1277,plain,
    ( spl8_2
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_19
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f729,f503,f246,f167,f89,f80])).

fof(f80,plain,
    ( spl8_2
  <=> r2_hidden(sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f89,plain,
    ( spl8_4
  <=> r2_hidden(sK3(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f167,plain,
    ( spl8_12
  <=> ! [X25,X24,X26] :
        ( ~ r2_hidden(X24,k9_relat_1(sK1,X25))
        | ~ r2_hidden(sK5(X24,X25,sK1),X26)
        | r2_hidden(X24,k9_relat_1(sK1,X26)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f246,plain,
    ( spl8_19
  <=> ! [X0] :
        ( ~ r2_hidden(sK3(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),X0)
        | r2_hidden(sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),k9_relat_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f503,plain,
    ( spl8_27
  <=> ! [X3,X2] :
        ( r2_hidden(sK5(X2,X3,sK1),k3_xboole_0(k1_relat_1(sK1),X3))
        | ~ r2_hidden(X2,k9_relat_1(sK1,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f729,plain,
    ( r2_hidden(sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)))
    | ~ spl8_4
    | ~ spl8_12
    | ~ spl8_19
    | ~ spl8_27 ),
    inference(resolution,[],[f720,f543])).

fof(f543,plain,
    ( ! [X33,X32] :
        ( ~ r2_hidden(X32,k9_relat_1(sK1,X33))
        | r2_hidden(X32,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X33))) )
    | ~ spl8_12
    | ~ spl8_27 ),
    inference(duplicate_literal_removal,[],[f542])).

fof(f542,plain,
    ( ! [X33,X32] :
        ( ~ r2_hidden(X32,k9_relat_1(sK1,X33))
        | ~ r2_hidden(X32,k9_relat_1(sK1,X33))
        | r2_hidden(X32,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),X33))) )
    | ~ spl8_12
    | ~ spl8_27 ),
    inference(resolution,[],[f504,f168])).

fof(f168,plain,
    ( ! [X26,X24,X25] :
        ( ~ r2_hidden(sK5(X24,X25,sK1),X26)
        | ~ r2_hidden(X24,k9_relat_1(sK1,X25))
        | r2_hidden(X24,k9_relat_1(sK1,X26)) )
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f167])).

fof(f504,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK5(X2,X3,sK1),k3_xboole_0(k1_relat_1(sK1),X3))
        | ~ r2_hidden(X2,k9_relat_1(sK1,X3)) )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f503])).

fof(f720,plain,
    ( r2_hidden(sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),k9_relat_1(sK1,sK0))
    | ~ spl8_4
    | ~ spl8_19 ),
    inference(resolution,[],[f247,f91])).

fof(f91,plain,
    ( r2_hidden(sK3(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),X0)
        | r2_hidden(sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),k9_relat_1(sK1,X0)) )
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f246])).

fof(f1273,plain,
    ( ~ spl8_2
    | spl8_5 ),
    inference(avatar_split_clause,[],[f329,f94,f80])).

fof(f94,plain,
    ( spl8_5
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(k4_tarski(X0,sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)))),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f329,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(k4_tarski(X0,sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)))),sK1)
      | ~ r2_hidden(sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))) ) ),
    inference(resolution,[],[f69,f53])).

fof(f53,plain,(
    ~ sQ7_eqProxy(k9_relat_1(sK1,sK0),k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))) ),
    inference(equality_proxy_replacement,[],[f28,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( sQ7_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ7_eqProxy])])).

fof(f28,plain,(
    k9_relat_1(sK1,sK0) != k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k9_relat_1(sK1,sK0) != k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,X0) != k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,sK0) != k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

fof(f69,plain,(
    ! [X17,X18,X16] :
      ( sQ7_eqProxy(k9_relat_1(sK1,X16),X17)
      | ~ r2_hidden(X18,X16)
      | ~ r2_hidden(k4_tarski(X18,sK2(sK1,X16,X17)),sK1)
      | ~ r2_hidden(sK2(sK1,X16,X17),X17) ) ),
    inference(resolution,[],[f27,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( sQ7_eqProxy(k9_relat_1(X0,X1),X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X4,sK2(X0,X1,X2)),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f34,f52])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(X4,sK2(X0,X1,X2)),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK2(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X0) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK4(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f16,f15,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK2(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X0) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f1253,plain,
    ( spl8_19
    | spl8_2
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f727,f177,f80,f246])).

fof(f177,plain,
    ( spl8_13
  <=> ! [X3,X5,X4] :
        ( ~ r2_hidden(sK3(sK1,X3,X4),X5)
        | r2_hidden(sK2(sK1,X3,X4),X4)
        | sQ7_eqProxy(k9_relat_1(sK1,X3),X4)
        | r2_hidden(sK2(sK1,X3,X4),k9_relat_1(sK1,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f727,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)))
        | ~ r2_hidden(sK3(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),X0)
        | r2_hidden(sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),k9_relat_1(sK1,X0)) )
    | ~ spl8_13 ),
    inference(resolution,[],[f178,f53])).

fof(f178,plain,
    ( ! [X4,X5,X3] :
        ( sQ7_eqProxy(k9_relat_1(sK1,X3),X4)
        | r2_hidden(sK2(sK1,X3,X4),X4)
        | ~ r2_hidden(sK3(sK1,X3,X4),X5)
        | r2_hidden(sK2(sK1,X3,X4),k9_relat_1(sK1,X5)) )
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f177])).

fof(f1219,plain,
    ( ~ spl8_2
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f1210,f94,f80,f80])).

fof(f1210,plain,
    ( ~ r2_hidden(sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)))
    | ~ spl8_2
    | ~ spl8_5 ),
    inference(resolution,[],[f523,f294])).

fof(f294,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(sK1,X1,sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)))),sK0)
        | ~ r2_hidden(sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),k9_relat_1(sK1,X1)) )
    | ~ spl8_5 ),
    inference(resolution,[],[f95,f68])).

fof(f68,plain,(
    ! [X14,X15] :
      ( r2_hidden(k4_tarski(sK4(sK1,X14,X15),X15),sK1)
      | ~ r2_hidden(X15,k9_relat_1(sK1,X14)) ) ),
    inference(resolution,[],[f27,f48])).

fof(f48,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)))),sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f523,plain,
    ( r2_hidden(sK4(sK1,k3_xboole_0(k1_relat_1(sK1),sK0),sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)))),sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f252,f50])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f252,plain,
    ( r2_hidden(sK4(sK1,k3_xboole_0(k1_relat_1(sK1),sK0),sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)))),k3_xboole_0(k1_relat_1(sK1),sK0))
    | ~ spl8_2 ),
    inference(resolution,[],[f82,f67])).

fof(f67,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X13,k9_relat_1(sK1,X12))
      | r2_hidden(sK4(sK1,X12,X13),X12) ) ),
    inference(resolution,[],[f27,f47])).

fof(f47,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,
    ( r2_hidden(sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f505,plain,
    ( ~ spl8_1
    | spl8_27 ),
    inference(avatar_split_clause,[],[f500,f503,f76])).

fof(f76,plain,
    ( spl8_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f500,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X3,sK1),k3_xboole_0(k1_relat_1(sK1),X3))
      | ~ r2_hidden(X2,k9_relat_1(sK1,X3))
      | ~ v1_relat_1(sK1) ) ),
    inference(duplicate_literal_removal,[],[f491])).

fof(f491,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK5(X2,X3,sK1),k3_xboole_0(k1_relat_1(sK1),X3))
      | ~ r2_hidden(X2,k9_relat_1(sK1,X3))
      | ~ r2_hidden(X2,k9_relat_1(sK1,X3))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f145,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f145,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK5(X4,X5,sK1),X6)
      | r2_hidden(sK5(X4,X5,sK1),k3_xboole_0(k1_relat_1(sK1),X6))
      | ~ r2_hidden(X4,k9_relat_1(sK1,X5)) ) ),
    inference(resolution,[],[f62,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1,sK1),k1_relat_1(sK1))
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f27,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f179,plain,
    ( ~ spl8_1
    | spl8_13 ),
    inference(avatar_split_clause,[],[f171,f177,f76])).

fof(f171,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK3(sK1,X3,X4),X5)
      | r2_hidden(sK2(sK1,X3,X4),k9_relat_1(sK1,X5))
      | sQ7_eqProxy(k9_relat_1(sK1,X3),X4)
      | r2_hidden(sK2(sK1,X3,X4),X4)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f66,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( sQ7_eqProxy(k9_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f32,f52])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X0)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X11,X9),sK1)
      | ~ r2_hidden(X11,X10)
      | r2_hidden(X9,k9_relat_1(sK1,X10)) ) ),
    inference(resolution,[],[f27,f46])).

fof(f46,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f169,plain,
    ( ~ spl8_1
    | spl8_12 ),
    inference(avatar_split_clause,[],[f157,f167,f76])).

fof(f157,plain,(
    ! [X26,X24,X25] :
      ( ~ r2_hidden(X24,k9_relat_1(sK1,X25))
      | r2_hidden(X24,k9_relat_1(sK1,X26))
      | ~ r2_hidden(sK5(X24,X25,sK1),X26)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f63,f46])).

fof(f63,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK5(X2,X3,sK1),X2),sK1)
      | ~ r2_hidden(X2,k9_relat_1(sK1,X3)) ) ),
    inference(resolution,[],[f27,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f98,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl8_1 ),
    inference(resolution,[],[f78,f27])).

fof(f78,plain,
    ( ~ v1_relat_1(sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f92,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_4 ),
    inference(avatar_split_clause,[],[f73,f89,f80,f76])).

fof(f73,plain,
    ( r2_hidden(sK3(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),sK0)
    | r2_hidden(sK2(sK1,sK0,k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),k9_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f53,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sQ7_eqProxy(k9_relat_1(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f33,f52])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
