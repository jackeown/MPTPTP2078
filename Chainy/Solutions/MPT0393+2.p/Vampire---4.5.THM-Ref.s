%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0393+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:28 EST 2020

% Result     : Theorem 6.83s
% Output     : Refutation 6.83s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 201 expanded)
%              Number of leaves         :   25 (  66 expanded)
%              Depth                    :   13
%              Number of atoms          :  491 ( 977 expanded)
%              Number of equality atoms :  126 ( 321 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7288,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1095,f1099,f1103,f2547,f2960,f6833,f6881,f7284])).

fof(f7284,plain,
    ( ~ spl31_12
    | ~ spl31_13
    | spl31_17 ),
    inference(avatar_contradiction_clause,[],[f7283])).

fof(f7283,plain,
    ( $false
    | ~ spl31_12
    | ~ spl31_13
    | spl31_17 ),
    inference(subsumption_resolution,[],[f7205,f7280])).

fof(f7280,plain,
    ( ! [X8] : r2_hidden(sK2(k1_tarski(sK0),sK0),X8)
    | ~ spl31_12
    | ~ spl31_13
    | spl31_17 ),
    inference(subsumption_resolution,[],[f7279,f6939])).

fof(f6939,plain,
    ( ! [X16] : r2_hidden(sK2(k1_tarski(sK0),sK0),k2_xboole_0(sK0,X16))
    | ~ spl31_13 ),
    inference(resolution,[],[f2958,f1041])).

fof(f1041,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f828])).

fof(f828,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f720])).

fof(f720,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
              & ~ r2_hidden(sK8(X0,X1,X2),X0) )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( r2_hidden(sK8(X0,X1,X2),X1)
            | r2_hidden(sK8(X0,X1,X2),X0)
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f718,f719])).

fof(f719,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            & ~ r2_hidden(sK8(X0,X1,X2),X0) )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( r2_hidden(sK8(X0,X1,X2),X1)
          | r2_hidden(sK8(X0,X1,X2),X0)
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f718,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f717])).

fof(f717,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f716])).

fof(f716,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f2958,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)
    | ~ spl31_13 ),
    inference(avatar_component_clause,[],[f2957])).

fof(f2957,plain,
    ( spl31_13
  <=> r2_hidden(sK2(k1_tarski(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_13])])).

fof(f7279,plain,
    ( ! [X8] :
        ( ~ r2_hidden(sK2(k1_tarski(sK0),sK0),k2_xboole_0(sK0,X8))
        | r2_hidden(sK2(k1_tarski(sK0),sK0),X8) )
    | ~ spl31_12
    | spl31_17 ),
    inference(forward_demodulation,[],[f7202,f7027])).

fof(f7027,plain,
    ( sK0 = sK3(k1_tarski(sK0),sK0)
    | ~ spl31_12 ),
    inference(resolution,[],[f2955,f1037])).

fof(f1037,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f799])).

fof(f799,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f707])).

fof(f707,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f705,f706])).

fof(f706,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f705,plain,(
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
    inference(rectify,[],[f704])).

fof(f704,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f2955,plain,
    ( r2_hidden(sK3(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ spl31_12 ),
    inference(avatar_component_clause,[],[f2953])).

fof(f2953,plain,
    ( spl31_12
  <=> r2_hidden(sK3(k1_tarski(sK0),sK0),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_12])])).

fof(f7202,plain,
    ( ! [X8] :
        ( r2_hidden(sK2(k1_tarski(sK0),sK0),X8)
        | ~ r2_hidden(sK2(k1_tarski(sK0),sK0),k2_xboole_0(sK3(k1_tarski(sK0),sK0),X8)) )
    | spl31_17 ),
    inference(resolution,[],[f6880,f1042])).

fof(f1042,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f827])).

fof(f827,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f720])).

fof(f6880,plain,
    ( ~ r2_hidden(sK2(k1_tarski(sK0),sK0),sK3(k1_tarski(sK0),sK0))
    | spl31_17 ),
    inference(avatar_component_clause,[],[f6878])).

fof(f6878,plain,
    ( spl31_17
  <=> r2_hidden(sK2(k1_tarski(sK0),sK0),sK3(k1_tarski(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_17])])).

fof(f7205,plain,
    ( ! [X11] : ~ r2_hidden(sK2(k1_tarski(sK0),sK0),k3_xboole_0(sK3(k1_tarski(sK0),sK0),X11))
    | spl31_17 ),
    inference(resolution,[],[f6880,f1047])).

fof(f1047,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f896])).

fof(f896,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f736])).

fof(f736,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
            | ~ r2_hidden(sK13(X0,X1,X2),X0)
            | ~ r2_hidden(sK13(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK13(X0,X1,X2),X1)
              & r2_hidden(sK13(X0,X1,X2),X0) )
            | r2_hidden(sK13(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f734,f735])).

fof(f735,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
          | ~ r2_hidden(sK13(X0,X1,X2),X0)
          | ~ r2_hidden(sK13(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK13(X0,X1,X2),X1)
            & r2_hidden(sK13(X0,X1,X2),X0) )
          | r2_hidden(sK13(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f734,plain,(
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
    inference(rectify,[],[f733])).

fof(f733,plain,(
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
    inference(flattening,[],[f732])).

fof(f732,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f6881,plain,
    ( ~ spl31_17
    | ~ spl31_13
    | ~ spl31_4 ),
    inference(avatar_split_clause,[],[f3622,f1101,f2957,f6878])).

fof(f1101,plain,
    ( spl31_4
  <=> ! [X3] :
        ( sK0 != X3
        | ~ r2_hidden(sK2(k1_tarski(sK0),X3),X3)
        | ~ r2_hidden(sK2(k1_tarski(sK0),X3),sK3(k1_tarski(sK0),X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_4])])).

fof(f3622,plain,
    ( ~ r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)
    | ~ r2_hidden(sK2(k1_tarski(sK0),sK0),sK3(k1_tarski(sK0),sK0))
    | ~ spl31_4 ),
    inference(equality_resolution,[],[f1102])).

fof(f1102,plain,
    ( ! [X3] :
        ( sK0 != X3
        | ~ r2_hidden(sK2(k1_tarski(sK0),X3),X3)
        | ~ r2_hidden(sK2(k1_tarski(sK0),X3),sK3(k1_tarski(sK0),X3)) )
    | ~ spl31_4 ),
    inference(avatar_component_clause,[],[f1101])).

fof(f6833,plain,
    ( ~ spl31_2
    | spl31_13 ),
    inference(avatar_contradiction_clause,[],[f6832])).

fof(f6832,plain,
    ( $false
    | ~ spl31_2
    | spl31_13 ),
    inference(subsumption_resolution,[],[f6752,f2959])).

fof(f2959,plain,
    ( ~ r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)
    | spl31_13 ),
    inference(avatar_component_clause,[],[f2957])).

fof(f6752,plain,
    ( r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)
    | ~ spl31_2
    | spl31_13 ),
    inference(resolution,[],[f3842,f1036])).

fof(f1036,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f1035])).

fof(f1035,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f800])).

fof(f800,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f707])).

fof(f3842,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(sK0))
        | r2_hidden(sK2(k1_tarski(sK0),sK0),X0) )
    | ~ spl31_2
    | spl31_13 ),
    inference(subsumption_resolution,[],[f3841,f2959])).

fof(f3841,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)
        | ~ r2_hidden(X0,k1_tarski(sK0))
        | r2_hidden(sK2(k1_tarski(sK0),sK0),X0) )
    | ~ spl31_2 ),
    inference(equality_resolution,[],[f1094])).

fof(f1094,plain,
    ( ! [X0,X1] :
        ( sK0 != X0
        | r2_hidden(sK2(k1_tarski(sK0),X0),X0)
        | ~ r2_hidden(X1,k1_tarski(sK0))
        | r2_hidden(sK2(k1_tarski(sK0),X0),X1) )
    | ~ spl31_2 ),
    inference(avatar_component_clause,[],[f1093])).

fof(f1093,plain,
    ( spl31_2
  <=> ! [X1,X0] :
        ( sK0 != X0
        | r2_hidden(sK2(k1_tarski(sK0),X0),X0)
        | ~ r2_hidden(X1,k1_tarski(sK0))
        | r2_hidden(sK2(k1_tarski(sK0),X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_2])])).

fof(f2960,plain,
    ( spl31_12
    | ~ spl31_13
    | ~ spl31_3 ),
    inference(avatar_split_clause,[],[f2951,f1097,f2957,f2953])).

fof(f1097,plain,
    ( spl31_3
  <=> ! [X2] :
        ( sK0 != X2
        | ~ r2_hidden(sK2(k1_tarski(sK0),X2),X2)
        | r2_hidden(sK3(k1_tarski(sK0),X2),k1_tarski(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_3])])).

fof(f2951,plain,
    ( ~ r2_hidden(sK2(k1_tarski(sK0),sK0),sK0)
    | r2_hidden(sK3(k1_tarski(sK0),sK0),k1_tarski(sK0))
    | ~ spl31_3 ),
    inference(equality_resolution,[],[f1098])).

fof(f1098,plain,
    ( ! [X2] :
        ( sK0 != X2
        | ~ r2_hidden(sK2(k1_tarski(sK0),X2),X2)
        | r2_hidden(sK3(k1_tarski(sK0),X2),k1_tarski(sK0)) )
    | ~ spl31_3 ),
    inference(avatar_component_clause,[],[f1097])).

fof(f2547,plain,(
    ~ spl31_1 ),
    inference(avatar_split_clause,[],[f2546,f1089])).

fof(f1089,plain,
    ( spl31_1
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl31_1])])).

fof(f2546,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f2476,f1314])).

fof(f1314,plain,(
    k1_xboole_0 = k3_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(sK0)) ),
    inference(resolution,[],[f1115,f874])).

fof(f874,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f727])).

fof(f727,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1115,plain,(
    r1_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(sK0)) ),
    inference(resolution,[],[f1087,f878])).

fof(f878,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f644])).

fof(f644,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f306])).

fof(f306,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f1087,plain,(
    ~ r2_hidden(k1_xboole_0,k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f1082,f1037])).

fof(f1082,plain,
    ( k1_xboole_0 != sK0
    | ~ r2_hidden(k1_xboole_0,k1_tarski(sK0)) ),
    inference(superposition,[],[f776,f792])).

fof(f792,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(cnf_transformation,[],[f581])).

fof(f581,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_setfam_1(X0)
      | ~ r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f559])).

fof(f559,axiom,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_xboole_0 = k1_setfam_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

fof(f776,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f693])).

fof(f693,plain,(
    sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f569,f692])).

fof(f692,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => sK0 != k1_setfam_1(k1_tarski(sK0)) ),
    introduced(choice_axiom,[])).

fof(f569,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f551])).

fof(f551,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f550])).

fof(f550,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f2476,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(k1_xboole_0),k1_tarski(sK0)) ),
    inference(resolution,[],[f2333,f927])).

fof(f927,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f665])).

fof(f665,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f409])).

fof(f409,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(f2333,plain,(
    ~ r2_hidden(sK0,k1_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f1316,f870])).

fof(f870,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f640])).

fof(f640,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f412])).

fof(f412,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_zfmisc_1)).

fof(f1316,plain,(
    r1_xboole_0(k1_tarski(sK0),k1_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f1115,f877])).

fof(f877,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f643])).

fof(f643,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1103,plain,
    ( spl31_1
    | spl31_4 ),
    inference(avatar_split_clause,[],[f1085,f1101,f1089])).

fof(f1085,plain,(
    ! [X3] :
      ( sK0 != X3
      | ~ r2_hidden(sK2(k1_tarski(sK0),X3),sK3(k1_tarski(sK0),X3))
      | ~ r2_hidden(sK2(k1_tarski(sK0),X3),X3)
      | k1_xboole_0 = k1_tarski(sK0) ) ),
    inference(superposition,[],[f776,f789])).

fof(f789,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
      | ~ r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f701])).

fof(f701,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ( ( ( ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
                  & r2_hidden(sK3(X0,X1),X0) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ! [X4] :
                    ( r2_hidden(sK2(X0,X1),X4)
                    | ~ r2_hidden(X4,X0) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ( ~ r2_hidden(X5,sK4(X0,X5))
                    & r2_hidden(sK4(X0,X5),X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f697,f700,f699,f698])).

fof(f698,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r2_hidden(X2,X3)
                & r2_hidden(X3,X0) )
            | ~ r2_hidden(X2,X1) )
          & ( ! [X4] :
                ( r2_hidden(X2,X4)
                | ~ r2_hidden(X4,X0) )
            | r2_hidden(X2,X1) ) )
     => ( ( ? [X3] :
              ( ~ r2_hidden(sK2(X0,X1),X3)
              & r2_hidden(X3,X0) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ! [X4] :
              ( r2_hidden(sK2(X0,X1),X4)
              | ~ r2_hidden(X4,X0) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f699,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(sK2(X0,X1),X3)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f700,plain,(
    ! [X5,X0] :
      ( ? [X6] :
          ( ~ r2_hidden(X5,X6)
          & r2_hidden(X6,X0) )
     => ( ~ r2_hidden(X5,sK4(X0,X5))
        & r2_hidden(sK4(X0,X5),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f697,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r2_hidden(X4,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ? [X6] :
                      ( ~ r2_hidden(X5,X6)
                      & r2_hidden(X6,X0) ) )
                & ( ! [X7] :
                      ( r2_hidden(X5,X7)
                      | ~ r2_hidden(X7,X0) )
                  | ~ r2_hidden(X5,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(rectify,[],[f696])).

fof(f696,plain,(
    ! [X0,X1] :
      ( ( ( ( k1_setfam_1(X0) = X1
            | k1_xboole_0 != X1 )
          & ( k1_xboole_0 = X1
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 != X0 )
      & ( ( ( k1_setfam_1(X0) = X1
            | ? [X2] :
                ( ( ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r2_hidden(X3,X0) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r2_hidden(X3,X0) )
                  | ~ r2_hidden(X2,X1) ) )
            | k1_setfam_1(X0) != X1 ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f580])).

fof(f580,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f544])).

fof(f544,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f1099,plain,
    ( spl31_1
    | spl31_3 ),
    inference(avatar_split_clause,[],[f1084,f1097,f1089])).

fof(f1084,plain,(
    ! [X2] :
      ( sK0 != X2
      | r2_hidden(sK3(k1_tarski(sK0),X2),k1_tarski(sK0))
      | ~ r2_hidden(sK2(k1_tarski(sK0),X2),X2)
      | k1_xboole_0 = k1_tarski(sK0) ) ),
    inference(superposition,[],[f776,f788])).

fof(f788,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK3(X0,X1),X0)
      | ~ r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f701])).

fof(f1095,plain,
    ( spl31_1
    | spl31_2 ),
    inference(avatar_split_clause,[],[f1083,f1093,f1089])).

fof(f1083,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | r2_hidden(sK2(k1_tarski(sK0),X0),X1)
      | ~ r2_hidden(X1,k1_tarski(sK0))
      | r2_hidden(sK2(k1_tarski(sK0),X0),X0)
      | k1_xboole_0 = k1_tarski(sK0) ) ),
    inference(superposition,[],[f776,f787])).

fof(f787,plain,(
    ! [X4,X0,X1] :
      ( k1_setfam_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X4)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f701])).
%------------------------------------------------------------------------------
