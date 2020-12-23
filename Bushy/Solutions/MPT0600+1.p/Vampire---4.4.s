%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t204_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:58 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 161 expanded)
%              Number of leaves         :   21 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  342 ( 683 expanded)
%              Number of equality atoms :   54 ( 103 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f344,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f127,f130,f146,f173,f185,f193,f295,f314,f325,f339,f343])).

fof(f343,plain,
    ( spl8_13
    | ~ spl8_16
    | ~ spl8_58 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f341,f123])).

fof(f123,plain,
    ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_13
  <=> ~ r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f341,plain,
    ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | ~ spl8_16
    | ~ spl8_58 ),
    inference(forward_demodulation,[],[f340,f145])).

fof(f145,plain,
    ( ! [X0] : k11_relat_1(sK2,X0) = k9_relat_1(sK2,k1_tarski(X0))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl8_16
  <=> ! [X0] : k11_relat_1(sK2,X0) = k9_relat_1(sK2,k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f340,plain,
    ( r2_hidden(sK1,k9_relat_1(sK2,k1_tarski(sK0)))
    | ~ spl8_58 ),
    inference(resolution,[],[f338,f72])).

fof(f72,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/relat_1__t204_relat_1.p',d1_tarski)).

fof(f338,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r2_hidden(sK1,k9_relat_1(sK2,X0)) )
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl8_58
  <=> ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r2_hidden(sK1,k9_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f339,plain,
    ( spl8_58
    | ~ spl8_10
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f327,f183,f119,f337])).

fof(f119,plain,
    ( spl8_10
  <=> r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f183,plain,
    ( spl8_24
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(k4_tarski(X0,X2),sK2)
        | r2_hidden(X2,k9_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f327,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r2_hidden(sK1,k9_relat_1(sK2,X0)) )
    | ~ spl8_10
    | ~ spl8_24 ),
    inference(resolution,[],[f120,f184])).

fof(f184,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X2),sK2)
        | ~ r2_hidden(X0,X1)
        | r2_hidden(X2,k9_relat_1(sK2,X1)) )
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f183])).

fof(f120,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f325,plain,
    ( spl8_11
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_28
    | ~ spl8_52 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | ~ spl8_11
    | ~ spl8_12
    | ~ spl8_16
    | ~ spl8_28
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f323,f126])).

fof(f126,plain,
    ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_12
  <=> r2_hidden(sK1,k11_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f323,plain,
    ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_28
    | ~ spl8_52 ),
    inference(forward_demodulation,[],[f322,f145])).

fof(f322,plain,
    ( ~ r2_hidden(sK1,k9_relat_1(sK2,k1_tarski(sK0)))
    | ~ spl8_11
    | ~ spl8_28
    | ~ spl8_52 ),
    inference(subsumption_resolution,[],[f320,f117])).

fof(f117,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl8_11
  <=> ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f320,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,k9_relat_1(sK2,k1_tarski(sK0)))
    | ~ spl8_28
    | ~ spl8_52 ),
    inference(superposition,[],[f192,f313])).

fof(f313,plain,
    ( sK0 = sK5(sK2,k1_tarski(sK0),sK1)
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl8_52
  <=> sK0 = sK5(sK2,k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK5(sK2,X1,X0),X0),sK2)
        | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) )
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl8_28
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK2,X1))
        | r2_hidden(k4_tarski(sK5(sK2,X1,X0),X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f314,plain,
    ( spl8_52
    | ~ spl8_12
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f300,f293,f125,f312])).

fof(f293,plain,
    ( spl8_48
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,k11_relat_1(sK2,X3))
        | sK5(sK2,k1_tarski(X3),X2) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f300,plain,
    ( sK0 = sK5(sK2,k1_tarski(sK0),sK1)
    | ~ spl8_12
    | ~ spl8_48 ),
    inference(resolution,[],[f294,f126])).

fof(f294,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k11_relat_1(sK2,X3))
        | sK5(sK2,k1_tarski(X3),X2) = X3 )
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f293])).

fof(f295,plain,
    ( spl8_48
    | ~ spl8_16
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f180,f171,f144,f293])).

fof(f171,plain,
    ( spl8_22
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK2,X1))
        | r2_hidden(sK5(sK2,X1,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f180,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k11_relat_1(sK2,X3))
        | sK5(sK2,k1_tarski(X3),X2) = X3 )
    | ~ spl8_16
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f178,f145])).

fof(f178,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k9_relat_1(sK2,k1_tarski(X3)))
        | sK5(sK2,k1_tarski(X3),X2) = X3 )
    | ~ spl8_22 ),
    inference(resolution,[],[f172,f73])).

fof(f73,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK2,X1,X0),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK2,X1)) )
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f171])).

fof(f193,plain,
    ( spl8_28
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f151,f78,f191])).

fof(f78,plain,
    ( spl8_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK2,X1))
        | r2_hidden(k4_tarski(sK5(sK2,X1,X0),X0),sK2) )
    | ~ spl8_0 ),
    inference(resolution,[],[f70,f79])).

fof(f79,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f78])).

fof(f70,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK4(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f35,f38,f37,f36])).

fof(f36,plain,(
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
              | ~ r2_hidden(k4_tarski(X4,sK3(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK3(X0,X1,X2)),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK4(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK5(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t204_relat_1.p',d13_relat_1)).

fof(f185,plain,
    ( spl8_24
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f147,f78,f183])).

fof(f147,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r2_hidden(k4_tarski(X0,X2),sK2)
        | r2_hidden(X2,k9_relat_1(sK2,X1)) )
    | ~ spl8_0 ),
    inference(resolution,[],[f68,f79])).

fof(f68,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | r2_hidden(X6,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f173,plain,
    ( spl8_22
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f139,f78,f171])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK2,X1))
        | r2_hidden(sK5(sK2,X1,X0),X1) )
    | ~ spl8_0 ),
    inference(resolution,[],[f69,f79])).

fof(f69,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | r2_hidden(sK5(X0,X1,X6),X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f146,plain,
    ( spl8_16
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f138,f78,f144])).

fof(f138,plain,
    ( ! [X0] : k11_relat_1(sK2,X0) = k9_relat_1(sK2,k1_tarski(X0))
    | ~ spl8_0 ),
    inference(resolution,[],[f50,f79])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t204_relat_1.p',d16_relat_1)).

fof(f130,plain,
    ( ~ spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f129,f125,f116])).

fof(f129,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f48,f126])).

fof(f48,plain,
    ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
      | r2_hidden(k4_tarski(sK0,sK1),sK2) )
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | r2_hidden(k4_tarski(X0,X1),X2) )
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(sK1,k11_relat_1(sK2,sK0))
        | ~ r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
        | r2_hidden(k4_tarski(sK0,sK1),sK2) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r2_hidden(X1,k11_relat_1(X2,X0))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
        | ~ r2_hidden(k4_tarski(X0,X1),X2) )
      & ( r2_hidden(X1,k11_relat_1(X2,X0))
        | r2_hidden(k4_tarski(X0,X1),X2) )
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <~> r2_hidden(X1,k11_relat_1(X2,X0)) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t204_relat_1.p',t204_relat_1)).

fof(f127,plain,
    ( spl8_10
    | spl8_12 ),
    inference(avatar_split_clause,[],[f47,f125,f119])).

fof(f47,plain,
    ( r2_hidden(sK1,k11_relat_1(sK2,sK0))
    | r2_hidden(k4_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f46,f78])).

fof(f46,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
