%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 123 expanded)
%              Number of leaves         :   10 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  257 ( 735 expanded)
%              Number of equality atoms :   36 ( 104 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f165,f173,f183,f230,f316,f335,f348])).

fof(f348,plain,
    ( ~ spl4_4
    | ~ spl4_8
    | spl4_6 ),
    inference(avatar_split_clause,[],[f337,f96,f332,f76])).

fof(f76,plain,
    ( spl4_4
  <=> r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f332,plain,
    ( spl4_8
  <=> r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f96,plain,
    ( spl4_6
  <=> r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f337,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK1)
    | ~ r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK0)
    | spl4_6 ),
    inference(resolution,[],[f98,f31])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f11])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
    inference(rectify,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f98,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f335,plain,
    ( ~ spl4_4
    | spl4_8
    | spl4_3 ),
    inference(avatar_split_clause,[],[f319,f72,f332,f76])).

fof(f72,plain,
    ( spl4_3
  <=> r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f319,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK1)
    | ~ r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK0)
    | spl4_3 ),
    inference(resolution,[],[f73,f34])).

fof(f34,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f73,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f316,plain,
    ( ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f97,f219,f32])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

% (5236)Refutation not found, incomplete strategy% (5236)------------------------------
% (5236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5236)Termination reason: Refutation not found, incomplete strategy

% (5236)Memory used [KB]: 10490
% (5236)Time elapsed: 0.061 s
% (5236)------------------------------
% (5236)------------------------------
fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f219,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f74,f35])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f74,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f97,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f230,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl4_3
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f77,f74,f36])).

fof(f36,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f77,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f183,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(avatar_split_clause,[],[f182,f96,f76,f72])).

fof(f182,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2] :
      ( k4_xboole_0(sK0,sK1) != X2
      | r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),X2),k3_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),X2),sK0)
      | ~ r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),X2),X2) ) ),
    inference(superposition,[],[f18,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f173,plain,
    ( spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f172,f96,f72])).

fof(f172,plain,
    ( ~ r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X1] :
      ( k4_xboole_0(sK0,sK1) != X1
      | ~ r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),X1),k3_xboole_0(sK0,sK1))
      | r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f18,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f165,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f164,f76,f72])).

fof(f164,plain,
    ( r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k4_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f18,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:09:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (5246)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.42  % (5246)Refutation not found, incomplete strategy% (5246)------------------------------
% 0.21/0.42  % (5246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (5246)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (5246)Memory used [KB]: 1535
% 0.21/0.42  % (5246)Time elapsed: 0.003 s
% 0.21/0.42  % (5246)------------------------------
% 0.21/0.42  % (5246)------------------------------
% 0.21/0.46  % (5240)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (5243)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (5233)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (5233)Refutation not found, incomplete strategy% (5233)------------------------------
% 0.21/0.47  % (5233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (5233)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (5233)Memory used [KB]: 6140
% 0.21/0.47  % (5233)Time elapsed: 0.059 s
% 0.21/0.47  % (5233)------------------------------
% 0.21/0.47  % (5233)------------------------------
% 0.21/0.47  % (5236)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (5243)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f349,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f165,f173,f183,f230,f316,f335,f348])).
% 0.21/0.47  fof(f348,plain,(
% 0.21/0.47    ~spl4_4 | ~spl4_8 | spl4_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f337,f96,f332,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl4_4 <=> r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.47  fof(f332,plain,(
% 0.21/0.47    spl4_8 <=> r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl4_6 <=> r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.47  fof(f337,plain,(
% 0.21/0.47    ~r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK1) | ~r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK0) | spl4_6),
% 0.21/0.47    inference(resolution,[],[f98,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(rectify,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(nnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ~r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | spl4_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f96])).
% 0.21/0.47  fof(f335,plain,(
% 0.21/0.47    ~spl4_4 | spl4_8 | spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f319,f72,f332,f76])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl4_3 <=> r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.47  fof(f319,plain,(
% 0.21/0.47    r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK1) | ~r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK0) | spl4_3),
% 0.21/0.47    inference(resolution,[],[f73,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(rectify,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.47    inference(nnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ~r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl4_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f72])).
% 0.21/0.47  fof(f316,plain,(
% 0.21/0.47    ~spl4_3 | ~spl4_6),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f305])).
% 0.21/0.47  fof(f305,plain,(
% 0.21/0.47    $false | (~spl4_3 | ~spl4_6)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f97,f219,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(equality_resolution,[],[f20])).
% 0.21/0.47  % (5236)Refutation not found, incomplete strategy% (5236)------------------------------
% 0.21/0.47  % (5236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (5236)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (5236)Memory used [KB]: 10490
% 0.21/0.47  % (5236)Time elapsed: 0.061 s
% 0.21/0.47  % (5236)------------------------------
% 0.21/0.47  % (5236)------------------------------
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f219,plain,(
% 0.21/0.47    ~r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK1) | ~spl4_3),
% 0.21/0.47    inference(resolution,[],[f74,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(equality_resolution,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~spl4_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f72])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~spl4_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f96])).
% 0.21/0.47  fof(f230,plain,(
% 0.21/0.47    ~spl4_3 | spl4_4),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f216])).
% 0.21/0.47  fof(f216,plain,(
% 0.21/0.47    $false | (~spl4_3 | spl4_4)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f77,f74,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(equality_resolution,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    ~r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK0) | spl4_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f76])).
% 0.21/0.47  fof(f183,plain,(
% 0.21/0.47    ~spl4_3 | ~spl4_4 | spl4_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f182,f96,f76,f72])).
% 0.21/0.47  fof(f182,plain,(
% 0.21/0.47    r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(equality_resolution,[],[f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2] : (k4_xboole_0(sK0,sK1) != X2 | r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),X2),k3_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),X2),sK0) | ~r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),X2),X2)) )),
% 0.21/0.47    inference(superposition,[],[f18,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f3])).
% 0.21/0.47  fof(f3,conjecture,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.47  fof(f173,plain,(
% 0.21/0.47    spl4_3 | ~spl4_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f172,f96,f72])).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    ~r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(equality_resolution,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X1] : (k4_xboole_0(sK0,sK1) != X1 | ~r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),X1),k3_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),X1),X1)) )),
% 0.21/0.48    inference(superposition,[],[f18,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    spl4_3 | spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f164,f76,f72])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 0.21/0.48    inference(equality_resolution,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(sK0,sK1) != X0 | r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK3(sK0,k3_xboole_0(sK0,sK1),X0),X0)) )),
% 0.21/0.48    inference(superposition,[],[f18,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (5243)------------------------------
% 0.21/0.48  % (5243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5243)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (5243)Memory used [KB]: 6268
% 0.21/0.48  % (5243)Time elapsed: 0.060 s
% 0.21/0.48  % (5243)------------------------------
% 0.21/0.48  % (5243)------------------------------
% 0.21/0.48  % (5232)Success in time 0.12 s
%------------------------------------------------------------------------------
