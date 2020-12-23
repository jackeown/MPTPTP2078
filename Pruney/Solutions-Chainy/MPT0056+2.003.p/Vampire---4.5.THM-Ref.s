%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 179 expanded)
%              Number of leaves         :   13 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  301 (1110 expanded)
%              Number of equality atoms :   39 ( 135 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1056,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f200,f236,f256,f275,f792,f794,f827,f905,f925,f975,f991,f1055])).

fof(f1055,plain,
    ( ~ spl5_6
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f1041])).

fof(f1041,plain,
    ( $false
    | ~ spl5_6
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f156,f204,f36])).

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

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f204,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl5_8
  <=> r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f156,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl5_6
  <=> r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f991,plain,
    ( ~ spl5_5
    | ~ spl5_8
    | spl5_2 ),
    inference(avatar_split_clause,[],[f977,f83,f202,f151])).

fof(f151,plain,
    ( spl5_5
  <=> r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f83,plain,
    ( spl5_2
  <=> r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f977,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1)
    | ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0)
    | spl5_2 ),
    inference(resolution,[],[f84,f31])).

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
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).

fof(f11,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f84,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f975,plain,
    ( ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f959])).

fof(f959,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f126,f156,f35])).

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

fof(f126,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_3
  <=> r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f925,plain,
    ( ~ spl5_2
    | spl5_3
    | spl5_4
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f882,f79,f129,f124,f83])).

fof(f129,plain,
    ( spl5_4
  <=> k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f79,plain,
    ( spl5_1
  <=> r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f882,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f81,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f81,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f905,plain,
    ( ~ spl5_1
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f874])).

fof(f874,plain,
    ( $false
    | ~ spl5_1
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f157,f81,f32])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f157,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f155])).

fof(f827,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f795])).

fof(f795,plain,
    ( $false
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f18,f131])).

fof(f131,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f18,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2)
   => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f794,plain,
    ( ~ spl5_3
    | spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f260,f79,f129,f124])).

fof(f260,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2)
    | spl5_1 ),
    inference(resolution,[],[f80,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f792,plain,
    ( ~ spl5_2
    | spl5_3
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f777])).

fof(f777,plain,
    ( $false
    | ~ spl5_2
    | spl5_3
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f108,f125,f157,f34])).

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

fof(f125,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f108,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f85,f32])).

fof(f85,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f275,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f261,f79,f155,f151])).

fof(f261,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0)
    | spl5_1 ),
    inference(resolution,[],[f80,f31])).

fof(f256,plain,
    ( ~ spl5_2
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl5_2
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f153,f85,f33])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f153,plain,
    ( ~ r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f151])).

fof(f236,plain,
    ( ~ spl5_1
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl5_1
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f81,f153,f33])).

fof(f200,plain,
    ( spl5_1
    | spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f185,f83,f129,f79])).

fof(f185,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | spl5_2 ),
    inference(resolution,[],[f84,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:14:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (3424)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.47  % (3425)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (3417)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (3424)Refutation not found, incomplete strategy% (3424)------------------------------
% 0.22/0.48  % (3424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (3416)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (3424)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (3424)Memory used [KB]: 10618
% 0.22/0.48  % (3424)Time elapsed: 0.008 s
% 0.22/0.48  % (3424)------------------------------
% 0.22/0.48  % (3424)------------------------------
% 0.22/0.48  % (3412)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (3420)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (3425)Refutation not found, incomplete strategy% (3425)------------------------------
% 0.22/0.49  % (3425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3425)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (3425)Memory used [KB]: 6012
% 0.22/0.49  % (3425)Time elapsed: 0.070 s
% 0.22/0.49  % (3425)------------------------------
% 0.22/0.49  % (3425)------------------------------
% 0.22/0.50  % (3426)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (3428)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (3410)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (3413)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (3410)Refutation not found, incomplete strategy% (3410)------------------------------
% 0.22/0.51  % (3410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3410)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3410)Memory used [KB]: 6140
% 0.22/0.51  % (3410)Time elapsed: 0.085 s
% 0.22/0.51  % (3410)------------------------------
% 0.22/0.51  % (3410)------------------------------
% 0.22/0.51  % (3413)Refutation not found, incomplete strategy% (3413)------------------------------
% 0.22/0.51  % (3413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3413)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3413)Memory used [KB]: 10490
% 0.22/0.51  % (3413)Time elapsed: 0.095 s
% 0.22/0.51  % (3413)------------------------------
% 0.22/0.51  % (3413)------------------------------
% 0.22/0.51  % (3415)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (3421)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (3421)Refutation not found, incomplete strategy% (3421)------------------------------
% 0.22/0.51  % (3421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3421)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3421)Memory used [KB]: 10618
% 0.22/0.51  % (3421)Time elapsed: 0.098 s
% 0.22/0.51  % (3421)------------------------------
% 0.22/0.51  % (3421)------------------------------
% 0.22/0.51  % (3430)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (3430)Refutation not found, incomplete strategy% (3430)------------------------------
% 0.22/0.51  % (3430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (3430)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (3430)Memory used [KB]: 10490
% 0.22/0.51  % (3430)Time elapsed: 0.096 s
% 0.22/0.51  % (3430)------------------------------
% 0.22/0.51  % (3430)------------------------------
% 0.22/0.52  % (3414)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.52  % (3423)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (3411)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (3423)Refutation not found, incomplete strategy% (3423)------------------------------
% 0.22/0.52  % (3423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3420)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (3422)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (3418)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.53  % (3419)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.53  % (3411)Refutation not found, incomplete strategy% (3411)------------------------------
% 0.22/0.53  % (3411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (3411)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (3411)Memory used [KB]: 10490
% 0.22/0.53  % (3411)Time elapsed: 0.102 s
% 0.22/0.53  % (3411)------------------------------
% 0.22/0.53  % (3411)------------------------------
% 0.22/0.53  % (3423)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (3423)Memory used [KB]: 1535
% 0.22/0.53  % (3423)Time elapsed: 0.107 s
% 0.22/0.53  % (3423)------------------------------
% 0.22/0.53  % (3423)------------------------------
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f1056,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f200,f236,f256,f275,f792,f794,f827,f905,f925,f975,f991,f1055])).
% 0.22/0.54  fof(f1055,plain,(
% 0.22/0.54    ~spl5_6 | spl5_8),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f1041])).
% 0.22/0.54  fof(f1041,plain,(
% 0.22/0.54    $false | (~spl5_6 | spl5_8)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f156,f204,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(rectify,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(flattening,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.54  fof(f204,plain,(
% 0.22/0.54    ~r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1) | spl5_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f202])).
% 0.22/0.54  fof(f202,plain,(
% 0.22/0.54    spl5_8 <=> r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2)) | ~spl5_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f155])).
% 0.22/0.54  fof(f155,plain,(
% 0.22/0.54    spl5_6 <=> r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.54  fof(f991,plain,(
% 0.22/0.54    ~spl5_5 | ~spl5_8 | spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f977,f83,f202,f151])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    spl5_5 <=> r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    spl5_2 <=> r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.54  fof(f977,plain,(
% 0.22/0.54    ~r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1) | ~r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0) | spl5_2),
% 0.22/0.54    inference(resolution,[],[f84,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(rectify,[],[f9])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(flattening,[],[f8])).
% 0.22/0.54  fof(f8,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ~r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1)) | spl5_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f83])).
% 0.22/0.54  fof(f975,plain,(
% 0.22/0.54    ~spl5_3 | ~spl5_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f959])).
% 0.22/0.54  fof(f959,plain,(
% 0.22/0.54    $false | (~spl5_3 | ~spl5_6)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f126,f156,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2) | ~spl5_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f124])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    spl5_3 <=> r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.54  fof(f925,plain,(
% 0.22/0.54    ~spl5_2 | spl5_3 | spl5_4 | ~spl5_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f882,f79,f129,f124,f83])).
% 0.22/0.54  fof(f129,plain,(
% 0.22/0.54    spl5_4 <=> k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    spl5_1 <=> r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.54  fof(f882,plain,(
% 0.22/0.54    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) | r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2) | ~r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1)) | ~spl5_1),
% 0.22/0.54    inference(resolution,[],[f81,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f79])).
% 0.22/0.54  fof(f905,plain,(
% 0.22/0.54    ~spl5_1 | spl5_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f874])).
% 0.22/0.54  fof(f874,plain,(
% 0.22/0.54    $false | (~spl5_1 | spl5_6)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f157,f81,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    ~r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2)) | spl5_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f155])).
% 0.22/0.54  fof(f827,plain,(
% 0.22/0.54    ~spl5_4),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f795])).
% 0.22/0.54  fof(f795,plain,(
% 0.22/0.54    $false | ~spl5_4),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f18,f131])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) | ~spl5_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f129])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,plain,(
% 0.22/0.54    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).
% 0.22/0.54  fof(f6,plain,(
% 0.22/0.54    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2) => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f5,plain,(
% 0.22/0.54    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.54    inference(negated_conjecture,[],[f3])).
% 0.22/0.54  fof(f3,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.54  fof(f794,plain,(
% 0.22/0.54    ~spl5_3 | spl5_4 | spl5_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f260,f79,f129,f124])).
% 0.22/0.54  fof(f260,plain,(
% 0.22/0.54    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) | ~r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2) | spl5_1),
% 0.22/0.54    inference(resolution,[],[f80,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ~r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f79])).
% 0.22/0.54  fof(f792,plain,(
% 0.22/0.54    ~spl5_2 | spl5_3 | spl5_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f777])).
% 0.22/0.54  fof(f777,plain,(
% 0.22/0.54    $false | (~spl5_2 | spl5_3 | spl5_6)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f108,f125,f157,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    ~r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK2) | spl5_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f124])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK1) | ~spl5_2),
% 0.22/0.54    inference(resolution,[],[f85,f32])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,sK1)) | ~spl5_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f83])).
% 0.22/0.54  fof(f275,plain,(
% 0.22/0.54    ~spl5_5 | ~spl5_6 | spl5_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f261,f79,f155,f151])).
% 0.22/0.54  fof(f261,plain,(
% 0.22/0.54    ~r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k4_xboole_0(sK1,sK2)) | ~r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0) | spl5_1),
% 0.22/0.54    inference(resolution,[],[f80,f31])).
% 0.22/0.54  fof(f256,plain,(
% 0.22/0.54    ~spl5_2 | spl5_5),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f237])).
% 0.22/0.54  fof(f237,plain,(
% 0.22/0.54    $false | (~spl5_2 | spl5_5)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f153,f85,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    ~r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),sK0) | spl5_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f151])).
% 0.22/0.54  fof(f236,plain,(
% 0.22/0.54    ~spl5_1 | spl5_5),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f222])).
% 0.22/0.54  fof(f222,plain,(
% 0.22/0.54    $false | (~spl5_1 | spl5_5)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f81,f153,f33])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    spl5_1 | spl5_4 | spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f185,f83,f129,f79])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) | r2_hidden(sK4(k3_xboole_0(sK0,sK1),sK2,k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | spl5_2),
% 0.22/0.54    inference(resolution,[],[f84,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (3420)------------------------------
% 0.22/0.54  % (3420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3420)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (3420)Memory used [KB]: 6652
% 0.22/0.54  % (3420)Time elapsed: 0.096 s
% 0.22/0.54  % (3420)------------------------------
% 0.22/0.54  % (3420)------------------------------
% 0.22/0.54  % (3409)Success in time 0.174 s
%------------------------------------------------------------------------------
