%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0549+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 288 expanded)
%              Number of leaves         :   29 ( 103 expanded)
%              Depth                    :   16
%              Number of atoms          :  408 (1112 expanded)
%              Number of equality atoms :   47 ( 109 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f624,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f71,f75,f129,f135,f141,f168,f187,f189,f387,f556,f575,f622])).

fof(f622,plain,
    ( spl8_2
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f621,f104,f73,f63,f66])).

fof(f66,plain,
    ( spl8_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f63,plain,
    ( spl8_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f73,plain,
    ( spl8_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f104,plain,
    ( spl8_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f621,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(duplicate_literal_removal,[],[f618])).

fof(f618,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(resolution,[],[f612,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f612,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK3(X4,sK0),k1_relat_1(sK1))
        | r1_xboole_0(X4,sK0) )
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(resolution,[],[f606,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f606,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_7 ),
    inference(resolution,[],[f605,f110])).

fof(f110,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_7 ),
    inference(resolution,[],[f105,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f105,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f605,plain,
    ( ! [X1] :
        ( r2_hidden(sK6(sK1,X1),k1_xboole_0)
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | ~ r2_hidden(X1,sK0) )
    | ~ spl8_1
    | ~ spl8_3 ),
    inference(superposition,[],[f326,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f326,plain,
    ( ! [X4,X3] :
        ( r2_hidden(sK6(sK1,X3),k9_relat_1(sK1,X4))
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | ~ r2_hidden(X3,X4) )
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f323])).

fof(f323,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,X4)
        | ~ r2_hidden(X3,k1_relat_1(sK1))
        | r2_hidden(sK6(sK1,X3),k9_relat_1(sK1,X4))
        | ~ r2_hidden(X3,k1_relat_1(sK1)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f321,f61])).

fof(f61,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK4(X0,X1),X3),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK4(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK6(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f321,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X2),sK1)
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(X2,k9_relat_1(sK1,X1)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f59,f74])).

fof(f74,plain,
    ( v1_relat_1(sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK7(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
            & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),X0),X2)
        & r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f575,plain,
    ( spl8_1
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f566,f554,f185,f104,f63])).

fof(f185,plain,
    ( spl8_16
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f554,plain,
    ( spl8_42
  <=> ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f566,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_42 ),
    inference(resolution,[],[f555,f280])).

fof(f280,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k1_xboole_0,X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(forward_demodulation,[],[f272,f186])).

fof(f186,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f185])).

fof(f272,plain,
    ( ! [X0] :
        ( k1_relat_1(k1_xboole_0) = X0
        | r2_hidden(sK4(k1_xboole_0,X0),X0) )
    | ~ spl8_7 ),
    inference(resolution,[],[f53,f110])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
      | k1_relat_1(X0) = X1
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f555,plain,
    ( ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f554])).

fof(f556,plain,
    ( ~ spl8_3
    | spl8_42
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f551,f73,f66,f554,f73])).

fof(f551,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
        | ~ v1_relat_1(sK1) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f548])).

fof(f548,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
        | ~ r2_hidden(X0,k9_relat_1(sK1,sK0))
        | ~ v1_relat_1(sK1) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f402,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f402,plain,
    ( ! [X5] :
        ( ~ r2_hidden(sK7(X5,sK0,sK1),k1_relat_1(sK1))
        | ~ r2_hidden(X5,k9_relat_1(sK1,sK0)) )
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(resolution,[],[f388,f112])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK7(X0,X1,sK1),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f58,f74])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK7(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f388,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f70,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f387,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,k1_xboole_0)
    | ~ v1_xboole_0(k9_relat_1(sK1,k1_xboole_0))
    | v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f189,plain,(
    ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | ~ spl8_13 ),
    inference(resolution,[],[f167,f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f3,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f167,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_relat_1(k1_xboole_0))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl8_13
  <=> ! [X2] : ~ m1_subset_1(X2,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f187,plain,
    ( spl8_16
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f183,f163,f185])).

fof(f163,plain,
    ( spl8_12
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f183,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_12 ),
    inference(resolution,[],[f164,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f164,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f168,plain,
    ( spl8_12
    | spl8_13
    | ~ spl8_3
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f161,f139,f73,f166,f163])).

fof(f139,plain,
    ( spl8_11
  <=> k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f161,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_relat_1(k1_xboole_0))
        | v1_xboole_0(k1_relat_1(k1_xboole_0)) )
    | ~ spl8_3
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f160,f140])).

fof(f140,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f139])).

fof(f160,plain,
    ( ! [X2] :
        ( v1_xboole_0(k1_relat_1(k1_xboole_0))
        | ~ m1_subset_1(X2,k1_relat_1(k9_relat_1(sK1,k1_xboole_0))) )
    | ~ spl8_3
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f153,f140])).

fof(f153,plain,
    ( ! [X2] :
        ( v1_xboole_0(k1_relat_1(k9_relat_1(sK1,k1_xboole_0)))
        | ~ m1_subset_1(X2,k1_relat_1(k9_relat_1(sK1,k1_xboole_0))) )
    | ~ spl8_3 ),
    inference(resolution,[],[f119,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f119,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_relat_1(k9_relat_1(sK1,k1_xboole_0)))
    | ~ spl8_3 ),
    inference(resolution,[],[f117,f61])).

fof(f117,plain,
    ( ! [X0] : ~ r2_hidden(X0,k9_relat_1(sK1,k1_xboole_0))
    | ~ spl8_3 ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK1,k1_xboole_0))
        | ~ r2_hidden(X0,k9_relat_1(sK1,k1_xboole_0)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f113,f112])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK7(X0,k1_xboole_0,sK1),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK1,k1_xboole_0)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f112,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(trivial_inequality_removal,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f83,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f83,plain,(
    ! [X2,X3,X1] :
      ( k1_xboole_0 != k3_xboole_0(X3,X2)
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f47,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f141,plain,
    ( spl8_11
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f137,f127,f139])).

fof(f127,plain,
    ( spl8_10
  <=> v1_xboole_0(k9_relat_1(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f137,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)
    | ~ spl8_10 ),
    inference(resolution,[],[f128,f43])).

fof(f128,plain,
    ( v1_xboole_0(k9_relat_1(sK1,k1_xboole_0))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f135,plain,(
    ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl8_9 ),
    inference(resolution,[],[f125,f44])).

fof(f125,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k9_relat_1(sK1,k1_xboole_0))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl8_9
  <=> ! [X0] : ~ m1_subset_1(X0,k9_relat_1(sK1,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f129,plain,
    ( spl8_9
    | spl8_10
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f118,f73,f127,f124])).

fof(f118,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK1,k1_xboole_0))
        | ~ m1_subset_1(X0,k9_relat_1(sK1,k1_xboole_0)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f117,f48])).

fof(f75,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f39,f73])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k9_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k9_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k9_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k9_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k9_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f71,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f40,f66,f63])).

fof(f40,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f68,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f41,f66,f63])).

fof(f41,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
