%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 140 expanded)
%              Number of leaves         :   23 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  280 ( 502 expanded)
%              Number of equality atoms :   58 ( 132 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f453,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f133,f157,f159,f342,f355,f368,f390,f449,f451])).

fof(f451,plain,
    ( spl9_3
    | spl9_1
    | spl9_3 ),
    inference(avatar_split_clause,[],[f394,f65,f53,f65])).

fof(f53,plain,
    ( spl9_1
  <=> sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f65,plain,
    ( spl9_3
  <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f394,plain,
    ( sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0)
    | spl9_3 ),
    inference(resolution,[],[f224,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f19,f22,f21,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f224,plain,
    ( ! [X0,X1] : ~ r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,X1))
    | spl9_3 ),
    inference(resolution,[],[f67,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f67,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f449,plain,
    ( spl9_9
    | ~ spl9_11 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | spl9_9
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f140,f164,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f164,plain,
    ( r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),sK1),sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl9_11
  <=> r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),sK1),sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f140,plain,
    ( ~ r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1)
    | spl9_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl9_9
  <=> r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f390,plain,
    ( spl9_9
    | spl9_11
    | spl9_2 ),
    inference(avatar_split_clause,[],[f389,f57,f162,f138])).

fof(f57,plain,
    ( spl9_2
  <=> sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f389,plain,
    ( r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),sK1),sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1)
    | spl9_2 ),
    inference(equality_resolution,[],[f281])).

fof(f281,plain,
    ( ! [X0] :
        ( sK1 != X0
        | r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),X0),sK2(k2_zfmisc_1(sK0,sK1),X0)),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),X0),X0) )
    | spl9_2 ),
    inference(superposition,[],[f59,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK4(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f16,f15,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f59,plain,
    ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f368,plain,(
    ~ spl9_14 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | ~ spl9_14 ),
    inference(unit_resulting_resolution,[],[f30,f353,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f9,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f353,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl9_14
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
      | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
          | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
        | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) != X1
        | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
              & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

fof(f355,plain,
    ( spl9_14
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f344,f142,f138,f352])).

fof(f142,plain,
    ( spl9_10
  <=> ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f344,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl9_10 ),
    inference(resolution,[],[f143,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f143,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f342,plain,
    ( ~ spl9_9
    | spl9_10
    | spl9_2 ),
    inference(avatar_split_clause,[],[f341,f57,f142,f138])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1) )
    | spl9_2 ),
    inference(equality_resolution,[],[f282])).

fof(f282,plain,
    ( ! [X2,X1] :
        ( sK1 != X1
        | ~ r2_hidden(k4_tarski(X2,sK2(k2_zfmisc_1(sK0,sK1),X1)),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),X1),X1) )
    | spl9_2 ),
    inference(superposition,[],[f59,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f159,plain,
    ( ~ spl9_3
    | spl9_4
    | spl9_1 ),
    inference(avatar_split_clause,[],[f158,f53,f69,f65])).

fof(f69,plain,
    ( spl9_4
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0) )
    | spl9_1 ),
    inference(equality_resolution,[],[f135])).

fof(f135,plain,
    ( ! [X2,X1] :
        ( sK0 != X1
        | ~ r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),X1),X2),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),X1),X1) )
    | spl9_1 ),
    inference(superposition,[],[f55,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,
    ( sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f157,plain,(
    ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f31,f100,f47])).

fof(f100,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl9_6
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f133,plain,
    ( ~ spl9_3
    | spl9_6
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f90,f69,f99,f65])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f70,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,sK1))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f60,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f32,f57,f53])).

fof(f32,plain,
    ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:46:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (15976)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (15967)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (15985)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.48  % (15967)Refutation not found, incomplete strategy% (15967)------------------------------
% 0.22/0.48  % (15967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (15973)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (15967)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (15967)Memory used [KB]: 6140
% 0.22/0.49  % (15967)Time elapsed: 0.061 s
% 0.22/0.49  % (15967)------------------------------
% 0.22/0.49  % (15967)------------------------------
% 0.22/0.49  % (15978)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (15979)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (15971)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (15972)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (15978)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f453,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f60,f133,f157,f159,f342,f355,f368,f390,f449,f451])).
% 0.22/0.50  fof(f451,plain,(
% 0.22/0.50    spl9_3 | spl9_1 | spl9_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f394,f65,f53,f65])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    spl9_1 <=> sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl9_3 <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.50  fof(f394,plain,(
% 0.22/0.50    sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) | r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0) | spl9_3),
% 0.22/0.50    inference(resolution,[],[f224,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f19,f22,f21,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.50    inference(rectify,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,X1))) ) | spl9_3),
% 0.22/0.50    inference(resolution,[],[f67,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.50    inference(nnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ~r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0) | spl9_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f65])).
% 0.22/0.50  fof(f449,plain,(
% 0.22/0.50    spl9_9 | ~spl9_11),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f436])).
% 0.22/0.50  fof(f436,plain,(
% 0.22/0.50    $false | (spl9_9 | ~spl9_11)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f140,f164,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.22/0.50    inference(nnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),sK1),sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1)) | ~spl9_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f162])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    spl9_11 <=> r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),sK1),sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    ~r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1) | spl9_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f138])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl9_9 <=> r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.50  fof(f390,plain,(
% 0.22/0.50    spl9_9 | spl9_11 | spl9_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f389,f57,f162,f138])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    spl9_2 <=> sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.50  fof(f389,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),sK1),sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1)) | r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1) | spl9_2),
% 0.22/0.50    inference(equality_resolution,[],[f281])).
% 0.22/0.50  fof(f281,plain,(
% 0.22/0.50    ( ! [X0] : (sK1 != X0 | r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),X0),sK2(k2_zfmisc_1(sK0,sK1),X0)),k2_zfmisc_1(sK0,sK1)) | r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),X0),X0)) ) | spl9_2),
% 0.22/0.50    inference(superposition,[],[f59,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f16,f15,f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.50    inference(rectify,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | spl9_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f57])).
% 0.22/0.50  fof(f368,plain,(
% 0.22/0.50    ~spl9_14),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f356])).
% 0.22/0.50  fof(f356,plain,(
% 0.22/0.50    $false | ~spl9_14),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f30,f353,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK8(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (r2_hidden(sK8(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f9,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.50  fof(f353,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl9_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f352])).
% 0.22/0.50  fof(f352,plain,(
% 0.22/0.50    spl9_14 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    k1_xboole_0 != sK0),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    (sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) != X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0) => ((sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ? [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) != X1 | k1_relat_1(k2_zfmisc_1(X0,X1)) != X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.50    inference(negated_conjecture,[],[f6])).
% 0.22/0.50  fof(f6,conjecture,(
% 0.22/0.50    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).
% 0.22/0.50  fof(f355,plain,(
% 0.22/0.50    spl9_14 | ~spl9_9 | ~spl9_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f344,f142,f138,f352])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    spl9_10 <=> ! [X0] : ~r2_hidden(k4_tarski(X0,sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.22/0.50  fof(f344,plain,(
% 0.22/0.50    ( ! [X1] : (~r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1) | ~r2_hidden(X1,sK0)) ) | ~spl9_10),
% 0.22/0.50    inference(resolution,[],[f143,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))) ) | ~spl9_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f142])).
% 0.22/0.50  fof(f342,plain,(
% 0.22/0.50    ~spl9_9 | spl9_10 | spl9_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f341,f57,f142,f138])).
% 0.22/0.50  fof(f341,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1)) ) | spl9_2),
% 0.22/0.50    inference(equality_resolution,[],[f282])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    ( ! [X2,X1] : (sK1 != X1 | ~r2_hidden(k4_tarski(X2,sK2(k2_zfmisc_1(sK0,sK1),X1)),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),X1),X1)) ) | spl9_2),
% 0.22/0.50    inference(superposition,[],[f59,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    ~spl9_3 | spl9_4 | spl9_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f158,f53,f69,f65])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl9_4 <=> ! [X0] : ~r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0)) ) | spl9_1),
% 0.22/0.50    inference(equality_resolution,[],[f135])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    ( ! [X2,X1] : (sK0 != X1 | ~r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),X1),X2),k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),X1),X1)) ) | spl9_1),
% 0.22/0.50    inference(superposition,[],[f55,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (k1_relat_1(X0) = X1 | ~r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl9_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f53])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ~spl9_6),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f145])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    $false | ~spl9_6),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f31,f100,f47])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | ~spl9_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f99])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl9_6 <=> ! [X0] : ~r2_hidden(X0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    k1_xboole_0 != sK1),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    ~spl9_3 | spl9_6 | ~spl9_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f90,f69,f99,f65])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0)) ) | ~spl9_4),
% 0.22/0.50    inference(resolution,[],[f70,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,sK1))) ) | ~spl9_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f69])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ~spl9_1 | ~spl9_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f57,f53])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1)) | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (15978)------------------------------
% 0.22/0.50  % (15978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15978)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (15978)Memory used [KB]: 6268
% 0.22/0.50  % (15978)Time elapsed: 0.081 s
% 0.22/0.50  % (15978)------------------------------
% 0.22/0.50  % (15978)------------------------------
% 0.22/0.50  % (15968)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (15983)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (15962)Success in time 0.138 s
%------------------------------------------------------------------------------
