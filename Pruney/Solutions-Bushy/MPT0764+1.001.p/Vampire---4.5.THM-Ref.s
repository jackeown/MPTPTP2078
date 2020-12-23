%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0764+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 355 expanded)
%              Number of leaves         :   41 ( 155 expanded)
%              Depth                    :   15
%              Number of atoms          :  802 (1817 expanded)
%              Number of equality atoms :   95 ( 249 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f342,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f105,f109,f113,f129,f138,f154,f161,f181,f190,f236,f248,f271,f278,f280,f289,f304,f308,f310,f319,f330,f341])).

fof(f341,plain,
    ( ~ spl10_26
    | ~ spl10_6
    | spl10_33 ),
    inference(avatar_split_clause,[],[f334,f328,f127,f266])).

fof(f266,plain,
    ( spl10_26
  <=> r2_hidden(sK5(sK0,sK1),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f127,plain,
    ( spl10_6
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK0))
        | r2_hidden(k4_tarski(X0,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f328,plain,
    ( spl10_33
  <=> r2_hidden(k4_tarski(sK5(sK0,sK1),sK5(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f334,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),k3_relat_1(sK0))
    | ~ spl10_6
    | spl10_33 ),
    inference(resolution,[],[f329,f128])).

fof(f128,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,X0),sK0)
        | ~ r2_hidden(X0,k3_relat_1(sK0)) )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f329,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK0,sK1),sK5(sK0,sK1)),sK0)
    | spl10_33 ),
    inference(avatar_component_clause,[],[f328])).

fof(f330,plain,
    ( ~ spl10_28
    | ~ spl10_33
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f326,f296,f328,f276])).

fof(f276,plain,
    ( spl10_28
  <=> r2_hidden(sK5(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f296,plain,
    ( spl10_30
  <=> sK5(sK0,sK1) = sK2(sK5(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f326,plain,
    ( ~ r2_hidden(k4_tarski(sK5(sK0,sK1),sK5(sK0,sK1)),sK0)
    | ~ r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl10_30 ),
    inference(superposition,[],[f59,f297])).

fof(f297,plain,
    ( sK5(sK0,sK1) = sK2(sK5(sK0,sK1))
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f296])).

fof(f59,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(X2,sK2(X2)),sK0)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ! [X2] :
        ( ( ~ r2_hidden(k4_tarski(X2,sK2(X2)),sK0)
          & r2_hidden(sK2(X2),sK1) )
        | ~ r2_hidden(X2,sK1) )
    & k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_relat_1(sK0))
    & v2_wellord1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                    & r2_hidden(X3,X1) )
                | ~ r2_hidden(X2,X1) )
            & k1_xboole_0 != X1
            & r1_tarski(X1,k3_relat_1(X0)) )
        & v2_wellord1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(sK0)) )
      & v2_wellord1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
                & r2_hidden(X3,X1) )
            | ~ r2_hidden(X2,X1) )
        & k1_xboole_0 != X1
        & r1_tarski(X1,k3_relat_1(sK0)) )
   => ( ! [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
              & r2_hidden(X3,sK1) )
          | ~ r2_hidden(X2,sK1) )
      & k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X2] :
      ( ? [X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
          & r2_hidden(X3,sK1) )
     => ( ~ r2_hidden(k4_tarski(X2,sK2(X2)),sK0)
        & r2_hidden(sK2(X2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & r2_hidden(X3,X1) )
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ( r2_hidden(X3,X1)
                         => r2_hidden(k4_tarski(X2,X3),X0) )
                      & r2_hidden(X2,X1) )
                & k1_xboole_0 != X1
                & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord1)).

fof(f319,plain,
    ( ~ spl10_12
    | ~ spl10_4
    | ~ spl10_2
    | ~ spl10_29 ),
    inference(avatar_split_clause,[],[f318,f287,f103,f111,f168])).

fof(f168,plain,
    ( spl10_12
  <=> v1_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f111,plain,
    ( spl10_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f103,plain,
    ( spl10_2
  <=> r1_tarski(sK1,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f287,plain,
    ( spl10_29
  <=> ! [X0] :
        ( ~ r1_tarski(sK1,k3_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_wellord1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f318,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_wellord1(sK0)
    | ~ spl10_2
    | ~ spl10_29 ),
    inference(resolution,[],[f288,f104])).

fof(f104,plain,
    ( r1_tarski(sK1,k3_relat_1(sK0))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k3_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_wellord1(X0) )
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f287])).

fof(f310,plain,
    ( ~ spl10_28
    | spl10_32 ),
    inference(avatar_split_clause,[],[f309,f302,f276])).

fof(f302,plain,
    ( spl10_32
  <=> r2_hidden(sK2(sK5(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f309,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | spl10_32 ),
    inference(resolution,[],[f303,f58])).

fof(f58,plain,(
    ! [X2] :
      ( r2_hidden(sK2(X2),sK1)
      | ~ r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f303,plain,
    ( ~ r2_hidden(sK2(sK5(sK0,sK1)),sK1)
    | spl10_32 ),
    inference(avatar_component_clause,[],[f302])).

fof(f308,plain,
    ( ~ spl10_32
    | ~ spl10_2
    | ~ spl10_8
    | spl10_31 ),
    inference(avatar_split_clause,[],[f306,f299,f149,f103,f302])).

fof(f149,plain,
    ( spl10_8
  <=> ! [X1,X2] :
        ( r2_hidden(X1,k3_relat_1(sK0))
        | ~ r1_tarski(X2,k3_relat_1(sK0))
        | ~ r2_hidden(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f299,plain,
    ( spl10_31
  <=> r2_hidden(sK2(sK5(sK0,sK1)),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f306,plain,
    ( ~ r2_hidden(sK2(sK5(sK0,sK1)),sK1)
    | ~ spl10_2
    | ~ spl10_8
    | spl10_31 ),
    inference(resolution,[],[f305,f104])).

fof(f305,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK0))
        | ~ r2_hidden(sK2(sK5(sK0,sK1)),X0) )
    | ~ spl10_8
    | spl10_31 ),
    inference(resolution,[],[f300,f150])).

fof(f150,plain,
    ( ! [X2,X1] :
        ( r2_hidden(X1,k3_relat_1(sK0))
        | ~ r1_tarski(X2,k3_relat_1(sK0))
        | ~ r2_hidden(X1,X2) )
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f149])).

fof(f300,plain,
    ( ~ r2_hidden(sK2(sK5(sK0,sK1)),k3_relat_1(sK0))
    | spl10_31 ),
    inference(avatar_component_clause,[],[f299])).

fof(f304,plain,
    ( ~ spl10_28
    | spl10_30
    | ~ spl10_31
    | ~ spl10_32
    | ~ spl10_4
    | ~ spl10_27 ),
    inference(avatar_split_clause,[],[f291,f269,f111,f302,f299,f296,f276])).

fof(f269,plain,
    ( spl10_27
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK0))
        | ~ r2_hidden(X1,sK1)
        | r2_hidden(sK5(sK0,sK1),k1_wellord1(sK0,X1))
        | sK5(sK0,sK1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f291,plain,
    ( ~ r2_hidden(sK2(sK5(sK0,sK1)),sK1)
    | ~ r2_hidden(sK2(sK5(sK0,sK1)),k3_relat_1(sK0))
    | sK5(sK0,sK1) = sK2(sK5(sK0,sK1))
    | ~ r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl10_4
    | ~ spl10_27 ),
    inference(resolution,[],[f270,f121])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_wellord1(sK0,sK2(X0)))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_4 ),
    inference(resolution,[],[f120,f59])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK0)
        | ~ r2_hidden(X0,k1_wellord1(sK0,X1)) )
    | ~ spl10_4 ),
    inference(resolution,[],[f95,f112])).

fof(f112,plain,
    ( v1_relat_1(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X4,X1),X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0)
                | sK8(X0,X1,X2) = X1
                | ~ r2_hidden(sK8(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0)
                  & sK8(X0,X1,X2) != X1 )
                | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0)
          | sK8(X0,X1,X2) = X1
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X1),X0)
            & sK8(X0,X1,X2) != X1 )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f270,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK0,sK1),k1_wellord1(sK0,X1))
        | ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,k3_relat_1(sK0))
        | sK5(sK0,sK1) = X1 )
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f269])).

fof(f289,plain,
    ( spl10_29
    | spl10_1
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f282,f152,f99,f287])).

fof(f99,plain,
    ( spl10_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f152,plain,
    ( spl10_9
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f282,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK1
        | ~ r1_tarski(sK1,k3_relat_1(X0))
        | ~ v1_wellord1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl10_9 ),
    inference(resolution,[],[f153,f63])).

fof(f63,plain,(
    ! [X0,X3] :
      ( r2_hidden(sK5(X0,X3),X3)
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k3_relat_1(X0))
      | ~ v1_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ( ! [X2] :
                ( ~ r1_xboole_0(k1_wellord1(X0,X2),sK4(X0))
                | ~ r2_hidden(X2,sK4(X0)) )
            & k1_xboole_0 != sK4(X0)
            & r1_tarski(sK4(X0),k3_relat_1(X0)) ) )
        & ( ! [X3] :
              ( ( r1_xboole_0(k1_wellord1(X0,sK5(X0,X3)),X3)
                & r2_hidden(sK5(X0,X3),X3) )
              | k1_xboole_0 = X3
              | ~ r1_tarski(X3,k3_relat_1(X0)) )
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f36,f38,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r1_xboole_0(k1_wellord1(X0,X2),X1)
              | ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1
          & r1_tarski(X1,k3_relat_1(X0)) )
     => ( ! [X2] :
            ( ~ r1_xboole_0(k1_wellord1(X0,X2),sK4(X0))
            | ~ r2_hidden(X2,sK4(X0)) )
        & k1_xboole_0 != sK4(X0)
        & r1_tarski(sK4(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( r1_xboole_0(k1_wellord1(X0,X4),X3)
          & r2_hidden(X4,X3) )
     => ( r1_xboole_0(k1_wellord1(X0,sK5(X0,X3)),X3)
        & r2_hidden(sK5(X0,X3),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r1_xboole_0(k1_wellord1(X0,X2),X1)
                  | ~ r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) )
        & ( ! [X3] :
              ( ? [X4] :
                  ( r1_xboole_0(k1_wellord1(X0,X4),X3)
                  & r2_hidden(X4,X3) )
              | k1_xboole_0 = X3
              | ~ r1_tarski(X3,k3_relat_1(X0)) )
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v1_wellord1(X0)
          | ? [X1] :
              ( ! [X2] :
                  ( ~ r1_xboole_0(k1_wellord1(X0,X2),X1)
                  | ~ r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( ? [X2] :
                  ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                  & r2_hidden(X2,X1) )
              | k1_xboole_0 = X1
              | ~ r1_tarski(X1,k3_relat_1(X0)) )
          | ~ v1_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_wellord1(X0)
      <=> ! [X1] :
            ( ? [X2] :
                ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                & r2_hidden(X2,X1) )
            | k1_xboole_0 = X1
            | ~ r1_tarski(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_wellord1(X0)
      <=> ! [X1] :
            ~ ( ! [X2] :
                  ~ ( r1_xboole_0(k1_wellord1(X0,X2),X1)
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_wellord1)).

fof(f153,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f152])).

fof(f280,plain,
    ( ~ spl10_4
    | ~ spl10_12
    | ~ spl10_2
    | spl10_1
    | spl10_28 ),
    inference(avatar_split_clause,[],[f279,f276,f99,f103,f168,f111])).

fof(f279,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,k3_relat_1(sK0))
    | ~ v1_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | spl10_28 ),
    inference(resolution,[],[f277,f63])).

fof(f277,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | spl10_28 ),
    inference(avatar_component_clause,[],[f276])).

fof(f278,plain,
    ( ~ spl10_28
    | ~ spl10_2
    | ~ spl10_8
    | spl10_26 ),
    inference(avatar_split_clause,[],[f273,f266,f149,f103,f276])).

fof(f273,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),sK1)
    | ~ spl10_2
    | ~ spl10_8
    | spl10_26 ),
    inference(resolution,[],[f272,f104])).

fof(f272,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK0))
        | ~ r2_hidden(sK5(sK0,sK1),X0) )
    | ~ spl10_8
    | spl10_26 ),
    inference(resolution,[],[f267,f150])).

fof(f267,plain,
    ( ~ r2_hidden(sK5(sK0,sK1),k3_relat_1(sK0))
    | spl10_26 ),
    inference(avatar_component_clause,[],[f266])).

fof(f271,plain,
    ( ~ spl10_26
    | spl10_27
    | ~ spl10_4
    | ~ spl10_15
    | ~ spl10_23 ),
    inference(avatar_split_clause,[],[f260,f234,f187,f111,f269,f266])).

fof(f187,plain,
    ( spl10_15
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k1_wellord1(sK0,sK5(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f234,plain,
    ( spl10_23
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),sK0)
        | r2_hidden(k4_tarski(X1,X0),sK0)
        | ~ r2_hidden(X0,k3_relat_1(sK0))
        | ~ r2_hidden(X1,k3_relat_1(sK0))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f260,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK0))
        | sK5(sK0,sK1) = X1
        | r2_hidden(sK5(sK0,sK1),k1_wellord1(sK0,X1))
        | ~ r2_hidden(sK5(sK0,sK1),k3_relat_1(sK0))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl10_4
    | ~ spl10_15
    | ~ spl10_23 ),
    inference(resolution,[],[f258,f188])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_wellord1(sK0,sK5(sK0,sK1)))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f187])).

fof(f258,plain,
    ( ! [X2,X1] :
        ( r2_hidden(X2,k1_wellord1(sK0,X1))
        | ~ r2_hidden(X2,k3_relat_1(sK0))
        | X1 = X2
        | r2_hidden(X1,k1_wellord1(sK0,X2))
        | ~ r2_hidden(X1,k3_relat_1(sK0)) )
    | ~ spl10_4
    | ~ spl10_23 ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,k3_relat_1(sK0))
        | ~ r2_hidden(X2,k3_relat_1(sK0))
        | X1 = X2
        | r2_hidden(X1,k1_wellord1(sK0,X2))
        | X1 = X2
        | r2_hidden(X2,k1_wellord1(sK0,X1)) )
    | ~ spl10_4
    | ~ spl10_23 ),
    inference(resolution,[],[f253,f143])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK0)
        | X0 = X1
        | r2_hidden(X0,k1_wellord1(sK0,X1)) )
    | ~ spl10_4 ),
    inference(resolution,[],[f94,f112])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | r2_hidden(X4,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f253,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k4_tarski(X1,X2),sK0)
        | ~ r2_hidden(X2,k3_relat_1(sK0))
        | ~ r2_hidden(X1,k3_relat_1(sK0))
        | X1 = X2
        | r2_hidden(X2,k1_wellord1(sK0,X1)) )
    | ~ spl10_4
    | ~ spl10_23 ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k4_tarski(X1,X2),sK0)
        | ~ r2_hidden(X2,k3_relat_1(sK0))
        | ~ r2_hidden(X1,k3_relat_1(sK0))
        | X1 = X2
        | X1 = X2
        | r2_hidden(X2,k1_wellord1(sK0,X1)) )
    | ~ spl10_4
    | ~ spl10_23 ),
    inference(resolution,[],[f235,f143])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK0)
        | r2_hidden(k4_tarski(X1,X0),sK0)
        | ~ r2_hidden(X0,k3_relat_1(sK0))
        | ~ r2_hidden(X1,k3_relat_1(sK0))
        | X0 = X1 )
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f234])).

fof(f248,plain,
    ( ~ spl10_4
    | ~ spl10_3
    | spl10_22 ),
    inference(avatar_split_clause,[],[f239,f231,f107,f111])).

fof(f107,plain,
    ( spl10_3
  <=> v2_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f231,plain,
    ( spl10_22
  <=> v6_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f239,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | spl10_22 ),
    inference(resolution,[],[f232,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(f232,plain,
    ( ~ v6_relat_2(sK0)
    | spl10_22 ),
    inference(avatar_component_clause,[],[f231])).

fof(f236,plain,
    ( ~ spl10_22
    | spl10_23
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f229,f111,f234,f231])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK0)
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK0))
        | ~ r2_hidden(X0,k3_relat_1(sK0))
        | ~ v6_relat_2(sK0)
        | r2_hidden(k4_tarski(X1,X0),sK0) )
    | ~ spl10_4 ),
    inference(resolution,[],[f68,f112])).

fof(f68,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X3),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
            & sK6(X0) != sK7(X0)
            & r2_hidden(sK7(X0),k3_relat_1(X0))
            & r2_hidden(sK6(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f41,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK7(X0),sK6(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK6(X0),sK7(X0)),X0)
        & sK6(X0) != sK7(X0)
        & r2_hidden(sK7(X0),k3_relat_1(X0))
        & r2_hidden(sK6(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(f190,plain,
    ( spl10_15
    | spl10_1
    | ~ spl10_2
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f184,f159,f103,f99,f187])).

fof(f159,plain,
    ( spl10_10
  <=> ! [X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK0))
        | k1_xboole_0 = X0
        | r1_xboole_0(k1_wellord1(sK0,sK5(sK0,X0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f184,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK1
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k1_wellord1(sK0,sK5(sK0,sK1))) )
    | ~ spl10_2
    | ~ spl10_10 ),
    inference(resolution,[],[f163,f104])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k3_relat_1(sK0))
        | k1_xboole_0 = X0
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,k1_wellord1(sK0,sK5(sK0,X0))) )
    | ~ spl10_10 ),
    inference(resolution,[],[f160,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f21,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f160,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_wellord1(sK0,sK5(sK0,X0)),X0)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k3_relat_1(sK0)) )
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f159])).

fof(f181,plain,
    ( ~ spl10_4
    | ~ spl10_3
    | spl10_12 ),
    inference(avatar_split_clause,[],[f180,f168,f107,f111])).

fof(f180,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | spl10_12 ),
    inference(resolution,[],[f178,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f178,plain,
    ( ~ v1_wellord1(sK0)
    | spl10_12 ),
    inference(avatar_component_clause,[],[f168])).

fof(f161,plain,
    ( ~ spl10_3
    | spl10_10
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f157,f111,f159,f107])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK0))
        | r1_xboole_0(k1_wellord1(sK0,sK5(sK0,X0)),X0)
        | k1_xboole_0 = X0
        | ~ v2_wellord1(sK0) )
    | ~ spl10_4 ),
    inference(resolution,[],[f156,f112])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | r1_xboole_0(k1_wellord1(X1,sK5(X1,X0)),X0)
      | k1_xboole_0 = X0
      | ~ v2_wellord1(X1) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | r1_xboole_0(k1_wellord1(X1,sK5(X1,X0)),X0)
      | ~ v1_relat_1(X1)
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f64,f78])).

fof(f64,plain,(
    ! [X0,X3] :
      ( ~ v1_wellord1(X0)
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k3_relat_1(X0))
      | r1_xboole_0(k1_wellord1(X0,sK5(X0,X3)),X3)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f154,plain,
    ( spl10_8
    | spl10_9
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f146,f103,f152,f149])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X1,k3_relat_1(sK0))
        | ~ r2_hidden(X1,X2)
        | ~ r1_tarski(X2,k3_relat_1(sK0)) )
    | ~ spl10_2 ),
    inference(resolution,[],[f142,f104])).

fof(f142,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( ~ r1_tarski(X7,X5)
      | ~ r2_hidden(X6,X7)
      | r2_hidden(X4,X5)
      | ~ r2_hidden(X4,X8)
      | ~ r1_tarski(X8,X5) ) ),
    inference(resolution,[],[f139,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X2)
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f92,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,X3)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X3) ) ),
    inference(resolution,[],[f116,f91])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,X1) ) ),
    inference(resolution,[],[f93,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

% (7507)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f138,plain,
    ( ~ spl10_4
    | ~ spl10_3
    | spl10_5 ),
    inference(avatar_split_clause,[],[f131,f124,f107,f111])).

fof(f124,plain,
    ( spl10_5
  <=> v1_relat_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f131,plain,
    ( ~ v2_wellord1(sK0)
    | ~ v1_relat_1(sK0)
    | spl10_5 ),
    inference(resolution,[],[f125,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f125,plain,
    ( ~ v1_relat_2(sK0)
    | spl10_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f129,plain,
    ( ~ spl10_5
    | spl10_6
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f122,f111,f127,f124])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK0))
        | ~ v1_relat_2(sK0)
        | r2_hidden(k4_tarski(X0,X0),sK0) )
    | ~ spl10_4 ),
    inference(resolution,[],[f60,f112])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | ~ v1_relat_2(X0)
      | r2_hidden(k4_tarski(X2,X2),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK3(X0),sK3(X0)),X0)
            & r2_hidden(sK3(X0),k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k4_tarski(X1,X1),X0)
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0),sK3(X0)),X0)
        & r2_hidden(sK3(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v1_relat_2(X0)
          | ? [X1] :
              ( ~ r2_hidden(k4_tarski(X1,X1),X0)
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1] :
              ( r2_hidden(k4_tarski(X1,X1),X0)
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(k4_tarski(X1,X1),X0)
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v1_relat_2(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k3_relat_1(X0))
           => r2_hidden(k4_tarski(X1,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

fof(f113,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f54,f111])).

fof(f54,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

% (7514)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f109,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f55,f107])).

fof(f55,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f105,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f56,f103])).

fof(f56,plain,(
    r1_tarski(sK1,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f101,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f57,f99])).

fof(f57,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

%------------------------------------------------------------------------------
