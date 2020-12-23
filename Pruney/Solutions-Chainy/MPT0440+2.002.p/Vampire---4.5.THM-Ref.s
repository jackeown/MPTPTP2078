%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:56 EST 2020

% Result     : Theorem 7.06s
% Output     : Refutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 507 expanded)
%              Number of leaves         :   36 ( 163 expanded)
%              Depth                    :   18
%              Number of atoms          :  599 (1338 expanded)
%              Number of equality atoms :  168 ( 585 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8882,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f234,f1538,f3060,f3370,f5170,f7559,f8881])).

fof(f8881,plain,
    ( spl28_2
    | spl28_131 ),
    inference(avatar_contradiction_clause,[],[f8880])).

fof(f8880,plain,
    ( $false
    | spl28_2
    | spl28_131 ),
    inference(subsumption_resolution,[],[f8879,f3280])).

fof(f3280,plain,
    ( k1_xboole_0 != k2_relat_1(sK12)
    | spl28_131 ),
    inference(avatar_component_clause,[],[f3279])).

fof(f3279,plain,
    ( spl28_131
  <=> k1_xboole_0 = k2_relat_1(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_131])])).

fof(f8879,plain,
    ( k1_xboole_0 = k2_relat_1(sK12)
    | spl28_2
    | spl28_131 ),
    inference(trivial_inequality_removal,[],[f8876])).

fof(f8876,plain,
    ( sK11 != sK11
    | k1_xboole_0 = k2_relat_1(sK12)
    | k2_relat_1(sK12) != k2_relat_1(sK12)
    | spl28_2
    | spl28_131 ),
    inference(superposition,[],[f3466,f8858])).

fof(f8858,plain,
    ( sK11 = sK22(k2_relat_1(sK12),sK11)
    | spl28_2
    | spl28_131 ),
    inference(subsumption_resolution,[],[f8801,f3280])).

fof(f8801,plain,
    ( k1_xboole_0 = k2_relat_1(sK12)
    | sK11 = sK22(k2_relat_1(sK12),sK11)
    | spl28_2 ),
    inference(trivial_inequality_removal,[],[f8791])).

fof(f8791,plain,
    ( k1_xboole_0 = k2_relat_1(sK12)
    | k2_relat_1(sK12) != k2_relat_1(sK12)
    | sK11 = sK22(k2_relat_1(sK12),sK11)
    | spl28_2 ),
    inference(resolution,[],[f3464,f3263])).

fof(f3263,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK12))
      | sK11 = X0 ) ),
    inference(resolution,[],[f3230,f213])).

fof(f213,plain,(
    ! [X0] : sP2(X0,k2_relat_1(X0)) ),
    inference(equality_resolution,[],[f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ~ sP2(X0,X1) )
      & ( sP2(X0,X1)
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> sP2(X0,X1) ) ),
    inference(definition_folding,[],[f21,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f3230,plain,(
    ! [X0,X1] :
      ( ~ sP2(sK12,X1)
      | ~ r2_hidden(X0,X1)
      | sK11 = X0 ) ),
    inference(resolution,[],[f3213,f130])).

fof(f130,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK18(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK16(X0,X1)),X0)
            | ~ r2_hidden(sK16(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK17(X0,X1),sK16(X0,X1)),X0)
            | r2_hidden(sK16(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK18(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17,sK18])],[f62,f65,f64,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK16(X0,X1)),X0)
          | ~ r2_hidden(sK16(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK16(X0,X1)),X0)
          | r2_hidden(sK16(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK16(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK17(X0,X1),sK16(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK18(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
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
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
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
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f3213,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),sK12)
      | sK11 = X6 ) ),
    inference(superposition,[],[f206,f1578])).

fof(f1578,plain,(
    sK12 = k2_zfmisc_1(k2_enumset1(sK10,sK10,sK10,sK10),k2_enumset1(sK11,sK11,sK11,sK11)) ),
    inference(superposition,[],[f196,f190])).

fof(f190,plain,(
    sK12 = k2_enumset1(k4_tarski(sK10,sK11),k4_tarski(sK10,sK11),k4_tarski(sK10,sK11),k4_tarski(sK10,sK11)) ),
    inference(definition_unfolding,[],[f109,f188])).

fof(f188,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f113,f186])).

fof(f186,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f123,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f123,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f113,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f109,plain,(
    sK12 = k1_tarski(k4_tarski(sK10,sK11)) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( k1_tarski(sK11) != k2_relat_1(sK12)
      | k1_tarski(sK10) != k1_relat_1(sK12) )
    & sK12 = k1_tarski(k4_tarski(sK10,sK11))
    & v1_relat_1(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f26,f49])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_tarski(X1) != k2_relat_1(X2)
          | k1_tarski(X0) != k1_relat_1(X2) )
        & k1_tarski(k4_tarski(X0,X1)) = X2
        & v1_relat_1(X2) )
   => ( ( k1_tarski(sK11) != k2_relat_1(sK12)
        | k1_tarski(sK10) != k1_relat_1(sK12) )
      & sK12 = k1_tarski(k4_tarski(sK10,sK11))
      & v1_relat_1(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( k1_tarski(X1) != k2_relat_1(X2)
        | k1_tarski(X0) != k1_relat_1(X2) )
      & k1_tarski(k4_tarski(X0,X1)) = X2
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( k1_tarski(k4_tarski(X0,X1)) = X2
         => ( k1_tarski(X1) = k2_relat_1(X2)
            & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

fof(f196,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f146,f186,f188,f186])).

fof(f146,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f206,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | X1 = X3 ) ),
    inference(definition_unfolding,[],[f181,f188])).

fof(f181,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f104])).

fof(f104,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f3464,plain,
    ( ! [X0] :
        ( r2_hidden(sK22(X0,sK11),X0)
        | k1_xboole_0 = X0
        | k2_relat_1(sK12) != X0 )
    | spl28_2 ),
    inference(superposition,[],[f233,f195])).

fof(f195,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK22(X0,X1),X0) ) ),
    inference(definition_unfolding,[],[f142,f188])).

fof(f142,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK22(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( sK22(X0,X1) != X1
        & r2_hidden(sK22(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f31,f75])).

fof(f75,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK22(X0,X1) != X1
        & r2_hidden(sK22(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f233,plain,
    ( k2_relat_1(sK12) != k2_enumset1(sK11,sK11,sK11,sK11)
    | spl28_2 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl28_2
  <=> k2_relat_1(sK12) = k2_enumset1(sK11,sK11,sK11,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_2])])).

fof(f3466,plain,
    ( ! [X1] :
        ( sK11 != sK22(X1,sK11)
        | k1_xboole_0 = X1
        | k2_relat_1(sK12) != X1 )
    | spl28_2 ),
    inference(superposition,[],[f233,f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | sK22(X0,X1) != X1 ) ),
    inference(definition_unfolding,[],[f143,f188])).

fof(f143,plain,(
    ! [X0,X1] :
      ( sK22(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f7559,plain,(
    spl28_65 ),
    inference(avatar_split_clause,[],[f7543,f1390])).

fof(f1390,plain,
    ( spl28_65
  <=> r2_hidden(k4_tarski(sK10,sK11),sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_65])])).

fof(f7543,plain,(
    r2_hidden(k4_tarski(sK10,sK11),sK12) ),
    inference(superposition,[],[f3123,f190])).

fof(f3123,plain,(
    ! [X0] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(resolution,[],[f1058,f725])).

fof(f725,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,sK12))
      | r2_hidden(X0,X2) ) ),
    inference(superposition,[],[f207,f190])).

fof(f207,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3)))
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f180,f188])).

fof(f180,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f1058,plain,(
    ! [X0] : r2_hidden(k4_tarski(X0,k4_tarski(sK10,sK11)),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),sK12)) ),
    inference(superposition,[],[f225,f190])).

fof(f225,plain,(
    ! [X2,X3] : r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) ),
    inference(equality_resolution,[],[f224])).

fof(f224,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))
      | X0 != X2 ) ),
    inference(equality_resolution,[],[f208])).

fof(f208,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))
      | X1 != X3
      | X0 != X2 ) ),
    inference(definition_unfolding,[],[f185,f188,f188])).

fof(f185,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
      | X1 != X3
      | X0 != X2 ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f106])).

fof(f106,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
        | X1 != X3
        | X0 != X2 )
      & ( ( X1 = X3
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))
    <=> ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(f5170,plain,
    ( spl28_1
    | spl28_115 ),
    inference(avatar_contradiction_clause,[],[f5169])).

fof(f5169,plain,
    ( $false
    | spl28_1
    | spl28_115 ),
    inference(subsumption_resolution,[],[f5168,f2889])).

fof(f2889,plain,
    ( k1_xboole_0 != k1_relat_1(sK12)
    | spl28_115 ),
    inference(avatar_component_clause,[],[f2888])).

fof(f2888,plain,
    ( spl28_115
  <=> k1_xboole_0 = k1_relat_1(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_115])])).

fof(f5168,plain,
    ( k1_xboole_0 = k1_relat_1(sK12)
    | spl28_1
    | spl28_115 ),
    inference(trivial_inequality_removal,[],[f5167])).

fof(f5167,plain,
    ( sK10 != sK10
    | k1_xboole_0 = k1_relat_1(sK12)
    | k1_relat_1(sK12) != k1_relat_1(sK12)
    | spl28_1
    | spl28_115 ),
    inference(superposition,[],[f3073,f5145])).

fof(f5145,plain,
    ( sK10 = sK22(k1_relat_1(sK12),sK10)
    | spl28_1
    | spl28_115 ),
    inference(subsumption_resolution,[],[f5133,f2889])).

fof(f5133,plain,
    ( k1_xboole_0 = k1_relat_1(sK12)
    | sK10 = sK22(k1_relat_1(sK12),sK10)
    | spl28_1 ),
    inference(trivial_inequality_removal,[],[f5124])).

fof(f5124,plain,
    ( k1_xboole_0 = k1_relat_1(sK12)
    | k1_relat_1(sK12) != k1_relat_1(sK12)
    | sK10 = sK22(k1_relat_1(sK12),sK10)
    | spl28_1 ),
    inference(resolution,[],[f3071,f3246])).

fof(f3246,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK12))
      | sK10 = X0 ) ),
    inference(resolution,[],[f3225,f214])).

fof(f214,plain,(
    ! [X0] : sP3(X0,k1_relat_1(X0)) ),
    inference(equality_resolution,[],[f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ~ sP3(X0,X1) )
      & ( sP3(X0,X1)
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> sP3(X0,X1) ) ),
    inference(definition_folding,[],[f20,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f3225,plain,(
    ! [X6,X5] :
      ( ~ sP3(sK12,X6)
      | ~ r2_hidden(X5,X6)
      | sK10 = X5 ) ),
    inference(resolution,[],[f3210,f136])).

fof(f136,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK21(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK19(X0,X1),X3),X0)
            | ~ r2_hidden(sK19(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK19(X0,X1),sK20(X0,X1)),X0)
            | r2_hidden(sK19(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK21(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19,sK20,sK21])],[f69,f72,f71,f70])).

fof(f70,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK19(X0,X1),X3),X0)
          | ~ r2_hidden(sK19(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK19(X0,X1),X4),X0)
          | r2_hidden(sK19(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK19(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK19(X0,X1),sK20(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK21(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
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
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
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
        | ~ sP3(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f3210,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK12)
      | sK10 = X0 ) ),
    inference(superposition,[],[f210,f1578])).

fof(f210,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f183,f188,f188])).

fof(f183,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f3071,plain,
    ( ! [X0] :
        ( r2_hidden(sK22(X0,sK10),X0)
        | k1_xboole_0 = X0
        | k1_relat_1(sK12) != X0 )
    | spl28_1 ),
    inference(superposition,[],[f229,f195])).

fof(f229,plain,
    ( k1_relat_1(sK12) != k2_enumset1(sK10,sK10,sK10,sK10)
    | spl28_1 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl28_1
  <=> k1_relat_1(sK12) = k2_enumset1(sK10,sK10,sK10,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_1])])).

fof(f3073,plain,
    ( ! [X1] :
        ( sK10 != sK22(X1,sK10)
        | k1_xboole_0 = X1
        | k1_relat_1(sK12) != X1 )
    | spl28_1 ),
    inference(superposition,[],[f229,f194])).

fof(f3370,plain,
    ( spl28_75
    | ~ spl28_131 ),
    inference(avatar_split_clause,[],[f3369,f3279,f1513])).

fof(f1513,plain,
    ( spl28_75
  <=> ! [X21] : ~ r2_hidden(X21,sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_75])])).

fof(f3369,plain,
    ( ! [X3] : ~ r2_hidden(X3,sK12)
    | ~ spl28_131 ),
    inference(subsumption_resolution,[],[f3363,f279])).

fof(f279,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f277])).

fof(f277,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f276,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f82])).

fof(f82,plain,(
    ! [X1,X3,X0] :
      ( ( sP4(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP4(X1,X3,X0) ) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X1,X3,X0] :
      ( ( sP4(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP4(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X1,X3,X0] :
      ( sP4(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f276,plain,(
    ! [X4,X3] :
      ( sP4(k1_xboole_0,X3,X4)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f147,f235])).

fof(f235,plain,(
    ! [X0] : sP5(X0,k1_xboole_0,X0) ),
    inference(superposition,[],[f215,f112])).

fof(f112,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f215,plain,(
    ! [X0,X1] : sP5(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( sP5(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP5(X0,X1,X2) )
      & ( sP5(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP5(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f41,f40])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( sP5(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP4(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f147,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP4(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ( ( ~ sP4(X1,sK23(X0,X1,X2),X0)
            | ~ r2_hidden(sK23(X0,X1,X2),X2) )
          & ( sP4(X1,sK23(X0,X1,X2),X0)
            | r2_hidden(sK23(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP4(X1,X4,X0) )
            & ( sP4(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f78,f79])).

fof(f79,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP4(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP4(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP4(X1,sK23(X0,X1,X2),X0)
          | ~ r2_hidden(sK23(X0,X1,X2),X2) )
        & ( sP4(X1,sK23(X0,X1,X2),X0)
          | r2_hidden(sK23(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP4(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP4(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP4(X1,X4,X0) )
            & ( sP4(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP4(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP4(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP4(X1,X3,X0) )
            & ( sP4(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f3363,plain,
    ( ! [X3] :
        ( r2_hidden(sK11,k1_xboole_0)
        | ~ r2_hidden(X3,sK12) )
    | ~ spl28_131 ),
    inference(duplicate_literal_removal,[],[f3358])).

fof(f3358,plain,
    ( ! [X3] :
        ( r2_hidden(sK11,k1_xboole_0)
        | ~ r2_hidden(X3,sK12)
        | ~ r2_hidden(X3,sK12) )
    | ~ spl28_131 ),
    inference(superposition,[],[f1292,f3281])).

fof(f3281,plain,
    ( k1_xboole_0 = k2_relat_1(sK12)
    | ~ spl28_131 ),
    inference(avatar_component_clause,[],[f3279])).

fof(f1292,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11,k2_relat_1(X0))
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,sK12) ) ),
    inference(resolution,[],[f697,f213])).

fof(f697,plain,(
    ! [X101,X99,X100] :
      ( ~ sP2(X100,X101)
      | r2_hidden(sK11,X101)
      | ~ r2_hidden(X99,X100)
      | ~ r2_hidden(X99,sK12) ) ),
    inference(superposition,[],[f131,f660])).

fof(f660,plain,(
    ! [X0] :
      ( k4_tarski(sK10,sK11) = X0
      | ~ r2_hidden(X0,sK12) ) ),
    inference(condensation,[],[f659])).

fof(f659,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK10,sK11) = X0
      | ~ r2_hidden(X0,sK12)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f657,f217])).

fof(f217,plain,(
    ! [X4,X2,X3,X1] :
      ( sP8(k4_tarski(X3,X4),X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(equality_resolution,[],[f172])).

fof(f172,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP8(X0,X1,X2)
      | k4_tarski(X3,X4) != X0
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X3,X2) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1,X2] :
      ( ( sP8(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ( k4_tarski(sK26(X0,X1,X2),sK27(X0,X1,X2)) = X0
          & r2_hidden(sK27(X0,X1,X2),X1)
          & r2_hidden(sK26(X0,X1,X2),X2) )
        | ~ sP8(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK26,sK27])],[f98,f99])).

fof(f99,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( k4_tarski(X5,X6) = X0
          & r2_hidden(X6,X1)
          & r2_hidden(X5,X2) )
     => ( k4_tarski(sK26(X0,X1,X2),sK27(X0,X1,X2)) = X0
        & r2_hidden(sK27(X0,X1,X2),X1)
        & r2_hidden(sK26(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
    ! [X0,X1,X2] :
      ( ( sP8(X0,X1,X2)
        | ! [X3,X4] :
            ( k4_tarski(X3,X4) != X0
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(X3,X2) ) )
      & ( ? [X5,X6] :
            ( k4_tarski(X5,X6) = X0
            & r2_hidden(X6,X1)
            & r2_hidden(X5,X2) )
        | ~ sP8(X0,X1,X2) ) ) ),
    inference(rectify,[],[f97])).

fof(f97,plain,(
    ! [X3,X1,X0] :
      ( ( sP8(X3,X1,X0)
        | ! [X4,X5] :
            ( k4_tarski(X4,X5) != X3
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X0) ) )
      & ( ? [X4,X5] :
            ( k4_tarski(X4,X5) = X3
            & r2_hidden(X5,X1)
            & r2_hidden(X4,X0) )
        | ~ sP8(X3,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X3,X1,X0] :
      ( sP8(X3,X1,X0)
    <=> ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X4,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f657,plain,(
    ! [X14,X12,X13] :
      ( ~ sP8(k4_tarski(X13,X12),sK12,X14)
      | k4_tarski(sK10,sK11) = X12 ) ),
    inference(resolution,[],[f651,f313])).

fof(f313,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_zfmisc_1(X2,X1))
      | ~ sP8(X0,X1,X2) ) ),
    inference(resolution,[],[f166,f218])).

fof(f218,plain,(
    ! [X0,X1] : sP9(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(equality_resolution,[],[f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( sP9(X0,X1,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ~ sP9(X0,X1,X2) )
      & ( sP9(X0,X1,X2)
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> sP9(X0,X1,X2) ) ),
    inference(definition_folding,[],[f11,f47,f46])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( sP9(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP8(X3,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f166,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP9(X0,X1,X2)
      | ~ sP8(X4,X1,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0,X1,X2] :
      ( ( sP9(X0,X1,X2)
        | ( ( ~ sP8(sK25(X0,X1,X2),X1,X0)
            | ~ r2_hidden(sK25(X0,X1,X2),X2) )
          & ( sP8(sK25(X0,X1,X2),X1,X0)
            | r2_hidden(sK25(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP8(X4,X1,X0) )
            & ( sP8(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP9(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25])],[f94,f95])).

fof(f95,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP8(X3,X1,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP8(X3,X1,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP8(sK25(X0,X1,X2),X1,X0)
          | ~ r2_hidden(sK25(X0,X1,X2),X2) )
        & ( sP8(sK25(X0,X1,X2),X1,X0)
          | r2_hidden(sK25(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( ( sP9(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP8(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP8(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP8(X4,X1,X0) )
            & ( sP8(X4,X1,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP9(X0,X1,X2) ) ) ),
    inference(rectify,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( ( sP9(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP8(X3,X1,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP8(X3,X1,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP8(X3,X1,X0) )
            & ( sP8(X3,X1,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP9(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f651,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,sK12))
      | k4_tarski(sK10,sK11) = X1 ) ),
    inference(superposition,[],[f206,f190])).

fof(f131,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X6,X5),X0)
      | r2_hidden(X5,X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f3060,plain,
    ( ~ spl28_65
    | ~ spl28_115 ),
    inference(avatar_contradiction_clause,[],[f3059])).

fof(f3059,plain,
    ( $false
    | ~ spl28_65
    | ~ spl28_115 ),
    inference(subsumption_resolution,[],[f3048,f279])).

fof(f3048,plain,
    ( r2_hidden(sK10,k1_xboole_0)
    | ~ spl28_65
    | ~ spl28_115 ),
    inference(backward_demodulation,[],[f1481,f2890])).

fof(f2890,plain,
    ( k1_xboole_0 = k1_relat_1(sK12)
    | ~ spl28_115 ),
    inference(avatar_component_clause,[],[f2888])).

fof(f1481,plain,
    ( r2_hidden(sK10,k1_relat_1(sK12))
    | ~ spl28_65 ),
    inference(resolution,[],[f1475,f214])).

fof(f1475,plain,
    ( ! [X1] :
        ( ~ sP3(sK12,X1)
        | r2_hidden(sK10,X1) )
    | ~ spl28_65 ),
    inference(resolution,[],[f1391,f137])).

fof(f137,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,X1)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1391,plain,
    ( r2_hidden(k4_tarski(sK10,sK11),sK12)
    | ~ spl28_65 ),
    inference(avatar_component_clause,[],[f1390])).

fof(f1538,plain,
    ( ~ spl28_65
    | ~ spl28_75 ),
    inference(avatar_contradiction_clause,[],[f1519])).

fof(f1519,plain,
    ( $false
    | ~ spl28_65
    | ~ spl28_75 ),
    inference(subsumption_resolution,[],[f1391,f1514])).

fof(f1514,plain,
    ( ! [X21] : ~ r2_hidden(X21,sK12)
    | ~ spl28_75 ),
    inference(avatar_component_clause,[],[f1513])).

fof(f234,plain,
    ( ~ spl28_1
    | ~ spl28_2 ),
    inference(avatar_split_clause,[],[f189,f231,f227])).

fof(f189,plain,
    ( k2_relat_1(sK12) != k2_enumset1(sK11,sK11,sK11,sK11)
    | k1_relat_1(sK12) != k2_enumset1(sK10,sK10,sK10,sK10) ),
    inference(definition_unfolding,[],[f110,f188,f188])).

fof(f110,plain,
    ( k1_tarski(sK11) != k2_relat_1(sK12)
    | k1_tarski(sK10) != k1_relat_1(sK12) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:15:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (18580)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (18588)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.54  % (18596)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (18597)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (18605)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.57  % (18578)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.58  % (18579)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.58  % (18594)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.58  % (18589)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.59  % (18590)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.59  % (18598)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.59  % (18603)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.59  % (18581)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.59  % (18585)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.59  % (18586)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.60  % (18574)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.60  % (18591)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.61  % (18604)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.61  % (18582)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.61  % (18575)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.63  % (18600)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.87/0.63  % (18577)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.87/0.64  % (18584)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 2.20/0.65  % (18576)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 2.20/0.65  % (18593)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.20/0.65  % (18602)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.20/0.65  % (18601)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.20/0.66  % (18595)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.20/0.66  % (18583)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.29/0.67  % (18592)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 3.62/0.87  % (18579)Time limit reached!
% 3.62/0.87  % (18579)------------------------------
% 3.62/0.87  % (18579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.62/0.87  % (18579)Termination reason: Time limit
% 3.62/0.87  
% 3.62/0.87  % (18579)Memory used [KB]: 8315
% 3.62/0.87  % (18579)Time elapsed: 0.424 s
% 3.62/0.87  % (18579)------------------------------
% 3.62/0.87  % (18579)------------------------------
% 3.98/0.93  % (18584)Time limit reached!
% 3.98/0.93  % (18584)------------------------------
% 3.98/0.93  % (18584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.98/0.94  % (18584)Termination reason: Time limit
% 3.98/0.94  % (18584)Termination phase: Saturation
% 3.98/0.94  
% 3.98/0.94  % (18584)Memory used [KB]: 11641
% 3.98/0.94  % (18584)Time elapsed: 0.500 s
% 3.98/0.94  % (18584)------------------------------
% 3.98/0.94  % (18584)------------------------------
% 4.50/0.95  % (18592)Time limit reached!
% 4.50/0.95  % (18592)------------------------------
% 4.50/0.95  % (18592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/0.95  % (18592)Termination reason: Time limit
% 4.50/0.95  
% 4.50/0.95  % (18592)Memory used [KB]: 14328
% 4.50/0.95  % (18592)Time elapsed: 0.517 s
% 4.50/0.95  % (18592)------------------------------
% 4.50/0.95  % (18592)------------------------------
% 4.50/0.95  % (18575)Time limit reached!
% 4.50/0.95  % (18575)------------------------------
% 4.50/0.95  % (18575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/0.95  % (18575)Termination reason: Time limit
% 4.50/0.95  
% 4.50/0.95  % (18575)Memory used [KB]: 7803
% 4.50/0.95  % (18575)Time elapsed: 0.504 s
% 4.50/0.95  % (18575)------------------------------
% 4.50/0.95  % (18575)------------------------------
% 4.50/0.95  % (18586)Time limit reached!
% 4.50/0.95  % (18586)------------------------------
% 4.50/0.95  % (18586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/0.96  % (18574)Time limit reached!
% 4.50/0.96  % (18574)------------------------------
% 4.50/0.96  % (18574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/0.96  % (18574)Termination reason: Time limit
% 4.50/0.96  
% 4.50/0.96  % (18574)Memory used [KB]: 4477
% 4.50/0.96  % (18574)Time elapsed: 0.521 s
% 4.50/0.96  % (18574)------------------------------
% 4.50/0.96  % (18574)------------------------------
% 4.72/0.97  % (18586)Termination reason: Time limit
% 4.72/0.97  
% 4.72/0.97  % (18586)Memory used [KB]: 8059
% 4.72/0.97  % (18586)Time elapsed: 0.520 s
% 4.72/0.97  % (18586)------------------------------
% 4.72/0.97  % (18586)------------------------------
% 4.72/1.00  % (18620)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 5.02/1.04  % (18581)Time limit reached!
% 5.02/1.04  % (18581)------------------------------
% 5.02/1.04  % (18581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.25/1.05  % (18591)Time limit reached!
% 5.25/1.05  % (18591)------------------------------
% 5.25/1.05  % (18591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.25/1.05  % (18581)Termination reason: Time limit
% 5.25/1.05  % (18581)Termination phase: Saturation
% 5.25/1.05  
% 5.25/1.05  % (18581)Memory used [KB]: 11257
% 5.25/1.05  % (18581)Time elapsed: 0.600 s
% 5.25/1.05  % (18581)------------------------------
% 5.25/1.05  % (18581)------------------------------
% 5.25/1.05  % (18591)Termination reason: Time limit
% 5.25/1.05  
% 5.25/1.05  % (18591)Memory used [KB]: 15479
% 5.25/1.05  % (18591)Time elapsed: 0.616 s
% 5.25/1.05  % (18591)------------------------------
% 5.25/1.05  % (18591)------------------------------
% 5.25/1.07  % (18628)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.25/1.07  % (18627)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.25/1.08  % (18636)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.25/1.08  % (18604)Time limit reached!
% 5.25/1.08  % (18604)------------------------------
% 5.25/1.08  % (18604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.25/1.08  % (18604)Termination reason: Time limit
% 5.25/1.08  
% 5.25/1.08  % (18604)Memory used [KB]: 8443
% 5.25/1.08  % (18604)Time elapsed: 0.623 s
% 5.25/1.08  % (18604)------------------------------
% 5.25/1.08  % (18604)------------------------------
% 5.25/1.08  % (18624)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 5.25/1.09  % (18641)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 6.09/1.18  % (18677)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.45/1.20  % (18675)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.45/1.21  % (18685)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.45/1.24  % (18596)Time limit reached!
% 6.45/1.24  % (18596)------------------------------
% 6.45/1.24  % (18596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.45/1.25  % (18596)Termination reason: Time limit
% 6.45/1.25  % (18596)Termination phase: Saturation
% 6.45/1.25  
% 6.45/1.25  % (18596)Memory used [KB]: 6908
% 6.45/1.25  % (18596)Time elapsed: 0.800 s
% 6.45/1.25  % (18596)------------------------------
% 6.45/1.25  % (18596)------------------------------
% 7.06/1.29  % (18603)Refutation found. Thanks to Tanya!
% 7.06/1.29  % SZS status Theorem for theBenchmark
% 7.06/1.29  % SZS output start Proof for theBenchmark
% 7.06/1.29  fof(f8882,plain,(
% 7.06/1.29    $false),
% 7.06/1.29    inference(avatar_sat_refutation,[],[f234,f1538,f3060,f3370,f5170,f7559,f8881])).
% 7.06/1.29  fof(f8881,plain,(
% 7.06/1.29    spl28_2 | spl28_131),
% 7.06/1.29    inference(avatar_contradiction_clause,[],[f8880])).
% 7.06/1.29  fof(f8880,plain,(
% 7.06/1.29    $false | (spl28_2 | spl28_131)),
% 7.06/1.29    inference(subsumption_resolution,[],[f8879,f3280])).
% 7.06/1.29  fof(f3280,plain,(
% 7.06/1.29    k1_xboole_0 != k2_relat_1(sK12) | spl28_131),
% 7.06/1.29    inference(avatar_component_clause,[],[f3279])).
% 7.06/1.29  fof(f3279,plain,(
% 7.06/1.29    spl28_131 <=> k1_xboole_0 = k2_relat_1(sK12)),
% 7.06/1.29    introduced(avatar_definition,[new_symbols(naming,[spl28_131])])).
% 7.06/1.29  fof(f8879,plain,(
% 7.06/1.29    k1_xboole_0 = k2_relat_1(sK12) | (spl28_2 | spl28_131)),
% 7.06/1.29    inference(trivial_inequality_removal,[],[f8876])).
% 7.06/1.29  fof(f8876,plain,(
% 7.06/1.29    sK11 != sK11 | k1_xboole_0 = k2_relat_1(sK12) | k2_relat_1(sK12) != k2_relat_1(sK12) | (spl28_2 | spl28_131)),
% 7.06/1.29    inference(superposition,[],[f3466,f8858])).
% 7.06/1.29  fof(f8858,plain,(
% 7.06/1.29    sK11 = sK22(k2_relat_1(sK12),sK11) | (spl28_2 | spl28_131)),
% 7.06/1.29    inference(subsumption_resolution,[],[f8801,f3280])).
% 7.06/1.29  fof(f8801,plain,(
% 7.06/1.29    k1_xboole_0 = k2_relat_1(sK12) | sK11 = sK22(k2_relat_1(sK12),sK11) | spl28_2),
% 7.06/1.29    inference(trivial_inequality_removal,[],[f8791])).
% 7.06/1.29  fof(f8791,plain,(
% 7.06/1.29    k1_xboole_0 = k2_relat_1(sK12) | k2_relat_1(sK12) != k2_relat_1(sK12) | sK11 = sK22(k2_relat_1(sK12),sK11) | spl28_2),
% 7.06/1.29    inference(resolution,[],[f3464,f3263])).
% 7.06/1.29  fof(f3263,plain,(
% 7.06/1.29    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK12)) | sK11 = X0) )),
% 7.06/1.29    inference(resolution,[],[f3230,f213])).
% 7.06/1.29  fof(f213,plain,(
% 7.06/1.29    ( ! [X0] : (sP2(X0,k2_relat_1(X0))) )),
% 7.06/1.29    inference(equality_resolution,[],[f134])).
% 7.06/1.29  fof(f134,plain,(
% 7.06/1.29    ( ! [X0,X1] : (sP2(X0,X1) | k2_relat_1(X0) != X1) )),
% 7.06/1.29    inference(cnf_transformation,[],[f67])).
% 7.06/1.29  fof(f67,plain,(
% 7.06/1.29    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ~sP2(X0,X1)) & (sP2(X0,X1) | k2_relat_1(X0) != X1))),
% 7.06/1.29    inference(nnf_transformation,[],[f37])).
% 7.06/1.29  fof(f37,plain,(
% 7.06/1.29    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> sP2(X0,X1))),
% 7.06/1.29    inference(definition_folding,[],[f21,f36])).
% 7.06/1.29  fof(f36,plain,(
% 7.06/1.29    ! [X0,X1] : (sP2(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 7.06/1.29    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 7.06/1.29  fof(f21,axiom,(
% 7.06/1.29    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 7.06/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 7.06/1.29  fof(f3230,plain,(
% 7.06/1.29    ( ! [X0,X1] : (~sP2(sK12,X1) | ~r2_hidden(X0,X1) | sK11 = X0) )),
% 7.06/1.29    inference(resolution,[],[f3213,f130])).
% 7.06/1.29  fof(f130,plain,(
% 7.06/1.29    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK18(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | ~sP2(X0,X1)) )),
% 7.06/1.29    inference(cnf_transformation,[],[f66])).
% 7.06/1.29  fof(f66,plain,(
% 7.06/1.29    ! [X0,X1] : ((sP2(X0,X1) | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK16(X0,X1)),X0) | ~r2_hidden(sK16(X0,X1),X1)) & (r2_hidden(k4_tarski(sK17(X0,X1),sK16(X0,X1)),X0) | r2_hidden(sK16(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK18(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | ~sP2(X0,X1)))),
% 7.06/1.29    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17,sK18])],[f62,f65,f64,f63])).
% 7.06/1.29  fof(f63,plain,(
% 7.06/1.29    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK16(X0,X1)),X0) | ~r2_hidden(sK16(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK16(X0,X1)),X0) | r2_hidden(sK16(X0,X1),X1))))),
% 7.06/1.29    introduced(choice_axiom,[])).
% 7.06/1.29  fof(f64,plain,(
% 7.06/1.29    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK16(X0,X1)),X0) => r2_hidden(k4_tarski(sK17(X0,X1),sK16(X0,X1)),X0))),
% 7.06/1.29    introduced(choice_axiom,[])).
% 7.06/1.29  fof(f65,plain,(
% 7.06/1.29    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK18(X0,X5),X5),X0))),
% 7.06/1.29    introduced(choice_axiom,[])).
% 7.06/1.29  fof(f62,plain,(
% 7.06/1.29    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | ~sP2(X0,X1)))),
% 7.06/1.29    inference(rectify,[],[f61])).
% 7.06/1.29  fof(f61,plain,(
% 7.06/1.29    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | ~sP2(X0,X1)))),
% 7.06/1.29    inference(nnf_transformation,[],[f36])).
% 7.06/1.29  fof(f3213,plain,(
% 7.06/1.29    ( ! [X6,X5] : (~r2_hidden(k4_tarski(X5,X6),sK12) | sK11 = X6) )),
% 7.06/1.29    inference(superposition,[],[f206,f1578])).
% 7.06/1.29  fof(f1578,plain,(
% 7.06/1.29    sK12 = k2_zfmisc_1(k2_enumset1(sK10,sK10,sK10,sK10),k2_enumset1(sK11,sK11,sK11,sK11))),
% 7.06/1.29    inference(superposition,[],[f196,f190])).
% 7.06/1.29  fof(f190,plain,(
% 7.06/1.29    sK12 = k2_enumset1(k4_tarski(sK10,sK11),k4_tarski(sK10,sK11),k4_tarski(sK10,sK11),k4_tarski(sK10,sK11))),
% 7.06/1.29    inference(definition_unfolding,[],[f109,f188])).
% 7.06/1.29  fof(f188,plain,(
% 7.06/1.29    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.06/1.29    inference(definition_unfolding,[],[f113,f186])).
% 7.06/1.29  fof(f186,plain,(
% 7.06/1.29    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.06/1.29    inference(definition_unfolding,[],[f123,f144])).
% 7.06/1.29  fof(f144,plain,(
% 7.06/1.29    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.06/1.29    inference(cnf_transformation,[],[f10])).
% 7.06/1.29  fof(f10,axiom,(
% 7.06/1.29    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.06/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 7.06/1.29  fof(f123,plain,(
% 7.06/1.29    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.06/1.29    inference(cnf_transformation,[],[f9])).
% 7.06/1.29  fof(f9,axiom,(
% 7.06/1.29    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.06/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 7.06/1.29  fof(f113,plain,(
% 7.06/1.29    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.06/1.29    inference(cnf_transformation,[],[f8])).
% 7.06/1.29  fof(f8,axiom,(
% 7.06/1.29    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.06/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 7.06/1.29  fof(f109,plain,(
% 7.06/1.29    sK12 = k1_tarski(k4_tarski(sK10,sK11))),
% 7.06/1.29    inference(cnf_transformation,[],[f50])).
% 7.06/1.29  fof(f50,plain,(
% 7.06/1.29    (k1_tarski(sK11) != k2_relat_1(sK12) | k1_tarski(sK10) != k1_relat_1(sK12)) & sK12 = k1_tarski(k4_tarski(sK10,sK11)) & v1_relat_1(sK12)),
% 7.06/1.29    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f26,f49])).
% 7.06/1.29  fof(f49,plain,(
% 7.06/1.29    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2)) => ((k1_tarski(sK11) != k2_relat_1(sK12) | k1_tarski(sK10) != k1_relat_1(sK12)) & sK12 = k1_tarski(k4_tarski(sK10,sK11)) & v1_relat_1(sK12))),
% 7.06/1.29    introduced(choice_axiom,[])).
% 7.06/1.29  fof(f26,plain,(
% 7.06/1.29    ? [X0,X1,X2] : ((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2 & v1_relat_1(X2))),
% 7.06/1.29    inference(flattening,[],[f25])).
% 7.06/1.29  fof(f25,plain,(
% 7.06/1.29    ? [X0,X1,X2] : (((k1_tarski(X1) != k2_relat_1(X2) | k1_tarski(X0) != k1_relat_1(X2)) & k1_tarski(k4_tarski(X0,X1)) = X2) & v1_relat_1(X2))),
% 7.06/1.29    inference(ennf_transformation,[],[f24])).
% 7.06/1.29  fof(f24,negated_conjecture,(
% 7.06/1.29    ~! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 7.06/1.29    inference(negated_conjecture,[],[f23])).
% 7.06/1.29  fof(f23,conjecture,(
% 7.06/1.29    ! [X0,X1,X2] : (v1_relat_1(X2) => (k1_tarski(k4_tarski(X0,X1)) = X2 => (k1_tarski(X1) = k2_relat_1(X2) & k1_tarski(X0) = k1_relat_1(X2))))),
% 7.06/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).
% 7.06/1.29  fof(f196,plain,(
% 7.06/1.29    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 7.06/1.29    inference(definition_unfolding,[],[f146,f186,f188,f186])).
% 7.06/1.29  fof(f146,plain,(
% 7.06/1.29    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 7.06/1.29    inference(cnf_transformation,[],[f17])).
% 7.06/1.29  fof(f17,axiom,(
% 7.06/1.29    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 7.06/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 7.06/1.29  fof(f206,plain,(
% 7.06/1.29    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | X1 = X3) )),
% 7.06/1.29    inference(definition_unfolding,[],[f181,f188])).
% 7.06/1.29  fof(f181,plain,(
% 7.06/1.29    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 7.06/1.29    inference(cnf_transformation,[],[f105])).
% 7.06/1.29  fof(f105,plain,(
% 7.06/1.29    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 7.06/1.29    inference(flattening,[],[f104])).
% 7.06/1.29  fof(f104,plain,(
% 7.06/1.29    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 7.06/1.29    inference(nnf_transformation,[],[f15])).
% 7.06/1.29  fof(f15,axiom,(
% 7.06/1.29    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 7.06/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 7.06/1.29  fof(f3464,plain,(
% 7.06/1.29    ( ! [X0] : (r2_hidden(sK22(X0,sK11),X0) | k1_xboole_0 = X0 | k2_relat_1(sK12) != X0) ) | spl28_2),
% 7.06/1.29    inference(superposition,[],[f233,f195])).
% 7.06/1.29  fof(f195,plain,(
% 7.06/1.29    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK22(X0,X1),X0)) )),
% 7.06/1.29    inference(definition_unfolding,[],[f142,f188])).
% 7.06/1.29  fof(f142,plain,(
% 7.06/1.29    ( ! [X0,X1] : (r2_hidden(sK22(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 7.06/1.29    inference(cnf_transformation,[],[f76])).
% 7.06/1.29  fof(f76,plain,(
% 7.06/1.29    ! [X0,X1] : ((sK22(X0,X1) != X1 & r2_hidden(sK22(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 7.06/1.29    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f31,f75])).
% 7.06/1.29  fof(f75,plain,(
% 7.06/1.29    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK22(X0,X1) != X1 & r2_hidden(sK22(X0,X1),X0)))),
% 7.06/1.29    introduced(choice_axiom,[])).
% 7.06/1.29  fof(f31,plain,(
% 7.06/1.29    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 7.06/1.29    inference(ennf_transformation,[],[f13])).
% 7.06/1.29  fof(f13,axiom,(
% 7.06/1.29    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 7.06/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 7.06/1.29  fof(f233,plain,(
% 7.06/1.29    k2_relat_1(sK12) != k2_enumset1(sK11,sK11,sK11,sK11) | spl28_2),
% 7.06/1.29    inference(avatar_component_clause,[],[f231])).
% 7.06/1.29  fof(f231,plain,(
% 7.06/1.29    spl28_2 <=> k2_relat_1(sK12) = k2_enumset1(sK11,sK11,sK11,sK11)),
% 7.06/1.29    introduced(avatar_definition,[new_symbols(naming,[spl28_2])])).
% 7.06/1.29  fof(f3466,plain,(
% 7.06/1.29    ( ! [X1] : (sK11 != sK22(X1,sK11) | k1_xboole_0 = X1 | k2_relat_1(sK12) != X1) ) | spl28_2),
% 7.06/1.29    inference(superposition,[],[f233,f194])).
% 7.06/1.29  fof(f194,plain,(
% 7.06/1.29    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | sK22(X0,X1) != X1) )),
% 7.06/1.29    inference(definition_unfolding,[],[f143,f188])).
% 7.06/1.29  fof(f143,plain,(
% 7.06/1.29    ( ! [X0,X1] : (sK22(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 7.06/1.29    inference(cnf_transformation,[],[f76])).
% 7.06/1.29  fof(f7559,plain,(
% 7.06/1.29    spl28_65),
% 7.06/1.29    inference(avatar_split_clause,[],[f7543,f1390])).
% 7.06/1.29  fof(f1390,plain,(
% 7.06/1.29    spl28_65 <=> r2_hidden(k4_tarski(sK10,sK11),sK12)),
% 7.06/1.29    introduced(avatar_definition,[new_symbols(naming,[spl28_65])])).
% 7.06/1.29  fof(f7543,plain,(
% 7.06/1.29    r2_hidden(k4_tarski(sK10,sK11),sK12)),
% 7.06/1.29    inference(superposition,[],[f3123,f190])).
% 7.06/1.29  fof(f3123,plain,(
% 7.06/1.29    ( ! [X0] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))) )),
% 7.06/1.29    inference(resolution,[],[f1058,f725])).
% 7.06/1.29  fof(f725,plain,(
% 7.06/1.29    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,sK12)) | r2_hidden(X0,X2)) )),
% 7.06/1.29    inference(superposition,[],[f207,f190])).
% 7.06/1.29  fof(f207,plain,(
% 7.06/1.29    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k2_enumset1(X3,X3,X3,X3))) | r2_hidden(X0,X2)) )),
% 7.06/1.29    inference(definition_unfolding,[],[f180,f188])).
% 7.06/1.29  fof(f180,plain,(
% 7.06/1.29    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 7.06/1.29    inference(cnf_transformation,[],[f105])).
% 7.06/1.29  fof(f1058,plain,(
% 7.06/1.29    ( ! [X0] : (r2_hidden(k4_tarski(X0,k4_tarski(sK10,sK11)),k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),sK12))) )),
% 7.06/1.29    inference(superposition,[],[f225,f190])).
% 7.06/1.29  fof(f225,plain,(
% 7.06/1.29    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3)))) )),
% 7.06/1.29    inference(equality_resolution,[],[f224])).
% 7.06/1.29  fof(f224,plain,(
% 7.06/1.29    ( ! [X2,X0,X3] : (r2_hidden(k4_tarski(X0,X3),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) | X0 != X2) )),
% 7.06/1.29    inference(equality_resolution,[],[f208])).
% 7.06/1.29  fof(f208,plain,(
% 7.06/1.29    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) | X1 != X3 | X0 != X2) )),
% 7.06/1.29    inference(definition_unfolding,[],[f185,f188,f188])).
% 7.06/1.29  fof(f185,plain,(
% 7.06/1.29    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) )),
% 7.06/1.29    inference(cnf_transformation,[],[f107])).
% 7.06/1.29  fof(f107,plain,(
% 7.06/1.29    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | X1 != X3 | X0 != X2) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 7.06/1.29    inference(flattening,[],[f106])).
% 7.06/1.29  fof(f106,plain,(
% 7.06/1.29    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) | (X1 != X3 | X0 != X2)) & ((X1 = X3 & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))))),
% 7.06/1.29    inference(nnf_transformation,[],[f16])).
% 7.06/1.29  fof(f16,axiom,(
% 7.06/1.29    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3))) <=> (X1 = X3 & X0 = X2))),
% 7.06/1.29    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).
% 7.06/1.29  fof(f5170,plain,(
% 7.06/1.29    spl28_1 | spl28_115),
% 7.06/1.29    inference(avatar_contradiction_clause,[],[f5169])).
% 7.06/1.30  fof(f5169,plain,(
% 7.06/1.30    $false | (spl28_1 | spl28_115)),
% 7.06/1.30    inference(subsumption_resolution,[],[f5168,f2889])).
% 7.06/1.30  fof(f2889,plain,(
% 7.06/1.30    k1_xboole_0 != k1_relat_1(sK12) | spl28_115),
% 7.06/1.30    inference(avatar_component_clause,[],[f2888])).
% 7.06/1.30  fof(f2888,plain,(
% 7.06/1.30    spl28_115 <=> k1_xboole_0 = k1_relat_1(sK12)),
% 7.06/1.30    introduced(avatar_definition,[new_symbols(naming,[spl28_115])])).
% 7.41/1.32  fof(f5168,plain,(
% 7.41/1.32    k1_xboole_0 = k1_relat_1(sK12) | (spl28_1 | spl28_115)),
% 7.41/1.32    inference(trivial_inequality_removal,[],[f5167])).
% 7.41/1.32  fof(f5167,plain,(
% 7.41/1.32    sK10 != sK10 | k1_xboole_0 = k1_relat_1(sK12) | k1_relat_1(sK12) != k1_relat_1(sK12) | (spl28_1 | spl28_115)),
% 7.41/1.32    inference(superposition,[],[f3073,f5145])).
% 7.41/1.32  fof(f5145,plain,(
% 7.41/1.32    sK10 = sK22(k1_relat_1(sK12),sK10) | (spl28_1 | spl28_115)),
% 7.41/1.32    inference(subsumption_resolution,[],[f5133,f2889])).
% 7.41/1.32  fof(f5133,plain,(
% 7.41/1.32    k1_xboole_0 = k1_relat_1(sK12) | sK10 = sK22(k1_relat_1(sK12),sK10) | spl28_1),
% 7.41/1.32    inference(trivial_inequality_removal,[],[f5124])).
% 7.41/1.32  fof(f5124,plain,(
% 7.41/1.32    k1_xboole_0 = k1_relat_1(sK12) | k1_relat_1(sK12) != k1_relat_1(sK12) | sK10 = sK22(k1_relat_1(sK12),sK10) | spl28_1),
% 7.41/1.32    inference(resolution,[],[f3071,f3246])).
% 7.41/1.32  fof(f3246,plain,(
% 7.41/1.32    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK12)) | sK10 = X0) )),
% 7.41/1.32    inference(resolution,[],[f3225,f214])).
% 7.41/1.32  fof(f214,plain,(
% 7.41/1.32    ( ! [X0] : (sP3(X0,k1_relat_1(X0))) )),
% 7.41/1.32    inference(equality_resolution,[],[f140])).
% 7.41/1.32  fof(f140,plain,(
% 7.41/1.32    ( ! [X0,X1] : (sP3(X0,X1) | k1_relat_1(X0) != X1) )),
% 7.41/1.32    inference(cnf_transformation,[],[f74])).
% 7.41/1.32  fof(f74,plain,(
% 7.41/1.32    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ~sP3(X0,X1)) & (sP3(X0,X1) | k1_relat_1(X0) != X1))),
% 7.41/1.32    inference(nnf_transformation,[],[f39])).
% 7.41/1.32  fof(f39,plain,(
% 7.41/1.32    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> sP3(X0,X1))),
% 7.41/1.32    inference(definition_folding,[],[f20,f38])).
% 7.41/1.32  fof(f38,plain,(
% 7.41/1.32    ! [X0,X1] : (sP3(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 7.41/1.32    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 7.41/1.32  fof(f20,axiom,(
% 7.41/1.32    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 7.41/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 7.41/1.32  fof(f3225,plain,(
% 7.41/1.32    ( ! [X6,X5] : (~sP3(sK12,X6) | ~r2_hidden(X5,X6) | sK10 = X5) )),
% 7.41/1.32    inference(resolution,[],[f3210,f136])).
% 7.41/1.32  fof(f136,plain,(
% 7.41/1.32    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK21(X0,X5)),X0) | ~r2_hidden(X5,X1) | ~sP3(X0,X1)) )),
% 7.41/1.32    inference(cnf_transformation,[],[f73])).
% 7.41/1.32  fof(f73,plain,(
% 7.41/1.32    ! [X0,X1] : ((sP3(X0,X1) | ((! [X3] : ~r2_hidden(k4_tarski(sK19(X0,X1),X3),X0) | ~r2_hidden(sK19(X0,X1),X1)) & (r2_hidden(k4_tarski(sK19(X0,X1),sK20(X0,X1)),X0) | r2_hidden(sK19(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK21(X0,X5)),X0) | ~r2_hidden(X5,X1))) | ~sP3(X0,X1)))),
% 7.41/1.32    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19,sK20,sK21])],[f69,f72,f71,f70])).
% 7.41/1.32  fof(f70,plain,(
% 7.41/1.32    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK19(X0,X1),X3),X0) | ~r2_hidden(sK19(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK19(X0,X1),X4),X0) | r2_hidden(sK19(X0,X1),X1))))),
% 7.41/1.32    introduced(choice_axiom,[])).
% 7.41/1.32  fof(f71,plain,(
% 7.41/1.32    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK19(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK19(X0,X1),sK20(X0,X1)),X0))),
% 7.41/1.32    introduced(choice_axiom,[])).
% 7.41/1.32  fof(f72,plain,(
% 7.41/1.32    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK21(X0,X5)),X0))),
% 7.41/1.32    introduced(choice_axiom,[])).
% 7.41/1.32  fof(f69,plain,(
% 7.41/1.32    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | ~sP3(X0,X1)))),
% 7.41/1.32    inference(rectify,[],[f68])).
% 7.41/1.32  fof(f68,plain,(
% 7.41/1.32    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | ~sP3(X0,X1)))),
% 7.41/1.32    inference(nnf_transformation,[],[f38])).
% 7.41/1.32  fof(f3210,plain,(
% 7.41/1.32    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK12) | sK10 = X0) )),
% 7.41/1.32    inference(superposition,[],[f210,f1578])).
% 7.41/1.32  fof(f210,plain,(
% 7.41/1.32    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X3,X3,X3,X3))) | X0 = X2) )),
% 7.41/1.32    inference(definition_unfolding,[],[f183,f188,f188])).
% 7.41/1.32  fof(f183,plain,(
% 7.41/1.32    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X3)))) )),
% 7.41/1.32    inference(cnf_transformation,[],[f107])).
% 7.41/1.32  fof(f3071,plain,(
% 7.41/1.32    ( ! [X0] : (r2_hidden(sK22(X0,sK10),X0) | k1_xboole_0 = X0 | k1_relat_1(sK12) != X0) ) | spl28_1),
% 7.41/1.32    inference(superposition,[],[f229,f195])).
% 7.41/1.32  fof(f229,plain,(
% 7.41/1.32    k1_relat_1(sK12) != k2_enumset1(sK10,sK10,sK10,sK10) | spl28_1),
% 7.41/1.32    inference(avatar_component_clause,[],[f227])).
% 7.41/1.32  fof(f227,plain,(
% 7.41/1.32    spl28_1 <=> k1_relat_1(sK12) = k2_enumset1(sK10,sK10,sK10,sK10)),
% 7.41/1.32    introduced(avatar_definition,[new_symbols(naming,[spl28_1])])).
% 7.41/1.32  fof(f3073,plain,(
% 7.41/1.32    ( ! [X1] : (sK10 != sK22(X1,sK10) | k1_xboole_0 = X1 | k1_relat_1(sK12) != X1) ) | spl28_1),
% 7.41/1.32    inference(superposition,[],[f229,f194])).
% 7.41/1.32  fof(f3370,plain,(
% 7.41/1.32    spl28_75 | ~spl28_131),
% 7.41/1.32    inference(avatar_split_clause,[],[f3369,f3279,f1513])).
% 7.41/1.32  fof(f1513,plain,(
% 7.41/1.32    spl28_75 <=> ! [X21] : ~r2_hidden(X21,sK12)),
% 7.41/1.32    introduced(avatar_definition,[new_symbols(naming,[spl28_75])])).
% 7.41/1.32  fof(f3369,plain,(
% 7.41/1.32    ( ! [X3] : (~r2_hidden(X3,sK12)) ) | ~spl28_131),
% 7.41/1.32    inference(subsumption_resolution,[],[f3363,f279])).
% 7.41/1.32  fof(f279,plain,(
% 7.41/1.32    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 7.41/1.32    inference(condensation,[],[f277])).
% 7.41/1.32  fof(f277,plain,(
% 7.41/1.32    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 7.41/1.32    inference(resolution,[],[f276,f152])).
% 7.41/1.32  fof(f152,plain,(
% 7.41/1.32    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 7.41/1.32    inference(cnf_transformation,[],[f83])).
% 7.41/1.32  fof(f83,plain,(
% 7.41/1.32    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP4(X0,X1,X2)))),
% 7.41/1.32    inference(rectify,[],[f82])).
% 7.41/1.32  fof(f82,plain,(
% 7.41/1.32    ! [X1,X3,X0] : ((sP4(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP4(X1,X3,X0)))),
% 7.41/1.32    inference(flattening,[],[f81])).
% 7.41/1.32  fof(f81,plain,(
% 7.41/1.32    ! [X1,X3,X0] : ((sP4(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP4(X1,X3,X0)))),
% 7.41/1.32    inference(nnf_transformation,[],[f40])).
% 7.41/1.32  fof(f40,plain,(
% 7.41/1.32    ! [X1,X3,X0] : (sP4(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 7.41/1.32    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 7.41/1.32  fof(f276,plain,(
% 7.41/1.32    ( ! [X4,X3] : (sP4(k1_xboole_0,X3,X4) | ~r2_hidden(X3,X4)) )),
% 7.41/1.32    inference(resolution,[],[f147,f235])).
% 7.41/1.32  fof(f235,plain,(
% 7.41/1.32    ( ! [X0] : (sP5(X0,k1_xboole_0,X0)) )),
% 7.41/1.32    inference(superposition,[],[f215,f112])).
% 7.41/1.32  fof(f112,plain,(
% 7.41/1.32    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.41/1.32    inference(cnf_transformation,[],[f6])).
% 7.41/1.32  fof(f6,axiom,(
% 7.41/1.32    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.41/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 7.41/1.32  fof(f215,plain,(
% 7.41/1.32    ( ! [X0,X1] : (sP5(X0,X1,k4_xboole_0(X0,X1))) )),
% 7.41/1.32    inference(equality_resolution,[],[f154])).
% 7.41/1.32  fof(f154,plain,(
% 7.41/1.32    ( ! [X2,X0,X1] : (sP5(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.41/1.32    inference(cnf_transformation,[],[f84])).
% 7.41/1.32  fof(f84,plain,(
% 7.41/1.32    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP5(X0,X1,X2)) & (sP5(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 7.41/1.32    inference(nnf_transformation,[],[f42])).
% 7.41/1.32  fof(f42,plain,(
% 7.41/1.32    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP5(X0,X1,X2))),
% 7.41/1.32    inference(definition_folding,[],[f2,f41,f40])).
% 7.41/1.32  fof(f41,plain,(
% 7.41/1.32    ! [X0,X1,X2] : (sP5(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP4(X1,X3,X0)))),
% 7.41/1.32    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 7.41/1.32  fof(f2,axiom,(
% 7.41/1.32    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.41/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 7.41/1.32  fof(f147,plain,(
% 7.41/1.32    ( ! [X4,X2,X0,X1] : (~sP5(X0,X1,X2) | ~r2_hidden(X4,X2) | sP4(X1,X4,X0)) )),
% 7.41/1.32    inference(cnf_transformation,[],[f80])).
% 7.41/1.32  fof(f80,plain,(
% 7.41/1.32    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ((~sP4(X1,sK23(X0,X1,X2),X0) | ~r2_hidden(sK23(X0,X1,X2),X2)) & (sP4(X1,sK23(X0,X1,X2),X0) | r2_hidden(sK23(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP4(X1,X4,X0)) & (sP4(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP5(X0,X1,X2)))),
% 7.41/1.32    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f78,f79])).
% 7.41/1.32  fof(f79,plain,(
% 7.41/1.32    ! [X2,X1,X0] : (? [X3] : ((~sP4(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP4(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP4(X1,sK23(X0,X1,X2),X0) | ~r2_hidden(sK23(X0,X1,X2),X2)) & (sP4(X1,sK23(X0,X1,X2),X0) | r2_hidden(sK23(X0,X1,X2),X2))))),
% 7.41/1.32    introduced(choice_axiom,[])).
% 7.41/1.32  fof(f78,plain,(
% 7.41/1.32    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ? [X3] : ((~sP4(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP4(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP4(X1,X4,X0)) & (sP4(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP5(X0,X1,X2)))),
% 7.41/1.32    inference(rectify,[],[f77])).
% 7.41/1.32  fof(f77,plain,(
% 7.41/1.32    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ? [X3] : ((~sP4(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP4(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP4(X1,X3,X0)) & (sP4(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP5(X0,X1,X2)))),
% 7.41/1.32    inference(nnf_transformation,[],[f41])).
% 7.41/1.32  fof(f3363,plain,(
% 7.41/1.32    ( ! [X3] : (r2_hidden(sK11,k1_xboole_0) | ~r2_hidden(X3,sK12)) ) | ~spl28_131),
% 7.41/1.32    inference(duplicate_literal_removal,[],[f3358])).
% 7.41/1.32  fof(f3358,plain,(
% 7.41/1.32    ( ! [X3] : (r2_hidden(sK11,k1_xboole_0) | ~r2_hidden(X3,sK12) | ~r2_hidden(X3,sK12)) ) | ~spl28_131),
% 7.41/1.32    inference(superposition,[],[f1292,f3281])).
% 7.41/1.32  fof(f3281,plain,(
% 7.41/1.32    k1_xboole_0 = k2_relat_1(sK12) | ~spl28_131),
% 7.41/1.32    inference(avatar_component_clause,[],[f3279])).
% 7.41/1.32  fof(f1292,plain,(
% 7.41/1.32    ( ! [X0,X1] : (r2_hidden(sK11,k2_relat_1(X0)) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,sK12)) )),
% 7.41/1.32    inference(resolution,[],[f697,f213])).
% 7.41/1.32  fof(f697,plain,(
% 7.41/1.32    ( ! [X101,X99,X100] : (~sP2(X100,X101) | r2_hidden(sK11,X101) | ~r2_hidden(X99,X100) | ~r2_hidden(X99,sK12)) )),
% 7.41/1.32    inference(superposition,[],[f131,f660])).
% 7.41/1.32  fof(f660,plain,(
% 7.41/1.32    ( ! [X0] : (k4_tarski(sK10,sK11) = X0 | ~r2_hidden(X0,sK12)) )),
% 7.41/1.32    inference(condensation,[],[f659])).
% 7.41/1.32  fof(f659,plain,(
% 7.41/1.32    ( ! [X2,X0,X1] : (k4_tarski(sK10,sK11) = X0 | ~r2_hidden(X0,sK12) | ~r2_hidden(X1,X2)) )),
% 7.41/1.32    inference(resolution,[],[f657,f217])).
% 7.41/1.32  fof(f217,plain,(
% 7.41/1.32    ( ! [X4,X2,X3,X1] : (sP8(k4_tarski(X3,X4),X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2)) )),
% 7.41/1.32    inference(equality_resolution,[],[f172])).
% 7.41/1.32  fof(f172,plain,(
% 7.41/1.32    ( ! [X4,X2,X0,X3,X1] : (sP8(X0,X1,X2) | k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2)) )),
% 7.41/1.32    inference(cnf_transformation,[],[f100])).
% 7.41/1.32  fof(f100,plain,(
% 7.41/1.32    ! [X0,X1,X2] : ((sP8(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & ((k4_tarski(sK26(X0,X1,X2),sK27(X0,X1,X2)) = X0 & r2_hidden(sK27(X0,X1,X2),X1) & r2_hidden(sK26(X0,X1,X2),X2)) | ~sP8(X0,X1,X2)))),
% 7.41/1.32    inference(skolemisation,[status(esa),new_symbols(skolem,[sK26,sK27])],[f98,f99])).
% 7.41/1.32  fof(f99,plain,(
% 7.41/1.32    ! [X2,X1,X0] : (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) => (k4_tarski(sK26(X0,X1,X2),sK27(X0,X1,X2)) = X0 & r2_hidden(sK27(X0,X1,X2),X1) & r2_hidden(sK26(X0,X1,X2),X2)))),
% 7.41/1.32    introduced(choice_axiom,[])).
% 7.41/1.32  fof(f98,plain,(
% 7.41/1.32    ! [X0,X1,X2] : ((sP8(X0,X1,X2) | ! [X3,X4] : (k4_tarski(X3,X4) != X0 | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X2))) & (? [X5,X6] : (k4_tarski(X5,X6) = X0 & r2_hidden(X6,X1) & r2_hidden(X5,X2)) | ~sP8(X0,X1,X2)))),
% 7.41/1.32    inference(rectify,[],[f97])).
% 7.41/1.32  fof(f97,plain,(
% 7.41/1.32    ! [X3,X1,X0] : ((sP8(X3,X1,X0) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~sP8(X3,X1,X0)))),
% 7.41/1.32    inference(nnf_transformation,[],[f46])).
% 7.41/1.32  fof(f46,plain,(
% 7.41/1.32    ! [X3,X1,X0] : (sP8(X3,X1,X0) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)))),
% 7.41/1.32    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 7.41/1.32  fof(f657,plain,(
% 7.41/1.32    ( ! [X14,X12,X13] : (~sP8(k4_tarski(X13,X12),sK12,X14) | k4_tarski(sK10,sK11) = X12) )),
% 7.41/1.32    inference(resolution,[],[f651,f313])).
% 7.41/1.32  fof(f313,plain,(
% 7.41/1.32    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_zfmisc_1(X2,X1)) | ~sP8(X0,X1,X2)) )),
% 7.41/1.32    inference(resolution,[],[f166,f218])).
% 7.41/1.32  fof(f218,plain,(
% 7.41/1.32    ( ! [X0,X1] : (sP9(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 7.41/1.32    inference(equality_resolution,[],[f173])).
% 7.41/1.32  fof(f173,plain,(
% 7.41/1.32    ( ! [X2,X0,X1] : (sP9(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 7.41/1.32    inference(cnf_transformation,[],[f101])).
% 7.41/1.32  fof(f101,plain,(
% 7.41/1.32    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ~sP9(X0,X1,X2)) & (sP9(X0,X1,X2) | k2_zfmisc_1(X0,X1) != X2))),
% 7.41/1.32    inference(nnf_transformation,[],[f48])).
% 7.41/1.32  fof(f48,plain,(
% 7.41/1.32    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> sP9(X0,X1,X2))),
% 7.41/1.32    inference(definition_folding,[],[f11,f47,f46])).
% 7.41/1.32  fof(f47,plain,(
% 7.41/1.32    ! [X0,X1,X2] : (sP9(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP8(X3,X1,X0)))),
% 7.41/1.32    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).
% 7.41/1.32  fof(f11,axiom,(
% 7.41/1.32    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 7.41/1.32    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 7.41/1.32  fof(f166,plain,(
% 7.41/1.32    ( ! [X4,X2,X0,X1] : (~sP9(X0,X1,X2) | ~sP8(X4,X1,X0) | r2_hidden(X4,X2)) )),
% 7.41/1.32    inference(cnf_transformation,[],[f96])).
% 7.41/1.32  fof(f96,plain,(
% 7.41/1.32    ! [X0,X1,X2] : ((sP9(X0,X1,X2) | ((~sP8(sK25(X0,X1,X2),X1,X0) | ~r2_hidden(sK25(X0,X1,X2),X2)) & (sP8(sK25(X0,X1,X2),X1,X0) | r2_hidden(sK25(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP8(X4,X1,X0)) & (sP8(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP9(X0,X1,X2)))),
% 7.41/1.32    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25])],[f94,f95])).
% 7.41/1.32  fof(f95,plain,(
% 7.41/1.32    ! [X2,X1,X0] : (? [X3] : ((~sP8(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP8(X3,X1,X0) | r2_hidden(X3,X2))) => ((~sP8(sK25(X0,X1,X2),X1,X0) | ~r2_hidden(sK25(X0,X1,X2),X2)) & (sP8(sK25(X0,X1,X2),X1,X0) | r2_hidden(sK25(X0,X1,X2),X2))))),
% 7.41/1.32    introduced(choice_axiom,[])).
% 7.41/1.32  fof(f94,plain,(
% 7.41/1.32    ! [X0,X1,X2] : ((sP9(X0,X1,X2) | ? [X3] : ((~sP8(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP8(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP8(X4,X1,X0)) & (sP8(X4,X1,X0) | ~r2_hidden(X4,X2))) | ~sP9(X0,X1,X2)))),
% 7.41/1.32    inference(rectify,[],[f93])).
% 7.41/1.32  fof(f93,plain,(
% 7.41/1.32    ! [X0,X1,X2] : ((sP9(X0,X1,X2) | ? [X3] : ((~sP8(X3,X1,X0) | ~r2_hidden(X3,X2)) & (sP8(X3,X1,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP8(X3,X1,X0)) & (sP8(X3,X1,X0) | ~r2_hidden(X3,X2))) | ~sP9(X0,X1,X2)))),
% 7.41/1.32    inference(nnf_transformation,[],[f47])).
% 7.41/1.32  fof(f651,plain,(
% 7.41/1.32    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,sK12)) | k4_tarski(sK10,sK11) = X1) )),
% 7.41/1.32    inference(superposition,[],[f206,f190])).
% 7.41/1.32  fof(f131,plain,(
% 7.41/1.32    ( ! [X6,X0,X5,X1] : (~r2_hidden(k4_tarski(X6,X5),X0) | r2_hidden(X5,X1) | ~sP2(X0,X1)) )),
% 7.41/1.32    inference(cnf_transformation,[],[f66])).
% 7.41/1.32  fof(f3060,plain,(
% 7.41/1.32    ~spl28_65 | ~spl28_115),
% 7.41/1.32    inference(avatar_contradiction_clause,[],[f3059])).
% 7.41/1.32  fof(f3059,plain,(
% 7.41/1.32    $false | (~spl28_65 | ~spl28_115)),
% 7.41/1.32    inference(subsumption_resolution,[],[f3048,f279])).
% 7.41/1.32  fof(f3048,plain,(
% 7.41/1.32    r2_hidden(sK10,k1_xboole_0) | (~spl28_65 | ~spl28_115)),
% 7.41/1.32    inference(backward_demodulation,[],[f1481,f2890])).
% 7.41/1.32  fof(f2890,plain,(
% 7.41/1.32    k1_xboole_0 = k1_relat_1(sK12) | ~spl28_115),
% 7.41/1.32    inference(avatar_component_clause,[],[f2888])).
% 7.41/1.32  fof(f1481,plain,(
% 7.41/1.32    r2_hidden(sK10,k1_relat_1(sK12)) | ~spl28_65),
% 7.41/1.32    inference(resolution,[],[f1475,f214])).
% 7.41/1.32  fof(f1475,plain,(
% 7.41/1.32    ( ! [X1] : (~sP3(sK12,X1) | r2_hidden(sK10,X1)) ) | ~spl28_65),
% 7.41/1.32    inference(resolution,[],[f1391,f137])).
% 7.41/1.32  fof(f137,plain,(
% 7.41/1.32    ( ! [X6,X0,X5,X1] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,X1) | ~sP3(X0,X1)) )),
% 7.41/1.32    inference(cnf_transformation,[],[f73])).
% 7.41/1.32  fof(f1391,plain,(
% 7.41/1.32    r2_hidden(k4_tarski(sK10,sK11),sK12) | ~spl28_65),
% 7.41/1.32    inference(avatar_component_clause,[],[f1390])).
% 7.41/1.32  fof(f1538,plain,(
% 7.41/1.32    ~spl28_65 | ~spl28_75),
% 7.41/1.32    inference(avatar_contradiction_clause,[],[f1519])).
% 7.41/1.32  fof(f1519,plain,(
% 7.41/1.32    $false | (~spl28_65 | ~spl28_75)),
% 7.41/1.32    inference(subsumption_resolution,[],[f1391,f1514])).
% 7.41/1.32  fof(f1514,plain,(
% 7.41/1.32    ( ! [X21] : (~r2_hidden(X21,sK12)) ) | ~spl28_75),
% 7.41/1.32    inference(avatar_component_clause,[],[f1513])).
% 7.41/1.32  fof(f234,plain,(
% 7.41/1.32    ~spl28_1 | ~spl28_2),
% 7.41/1.32    inference(avatar_split_clause,[],[f189,f231,f227])).
% 7.41/1.32  fof(f189,plain,(
% 7.41/1.32    k2_relat_1(sK12) != k2_enumset1(sK11,sK11,sK11,sK11) | k1_relat_1(sK12) != k2_enumset1(sK10,sK10,sK10,sK10)),
% 7.41/1.32    inference(definition_unfolding,[],[f110,f188,f188])).
% 7.41/1.32  fof(f110,plain,(
% 7.41/1.32    k1_tarski(sK11) != k2_relat_1(sK12) | k1_tarski(sK10) != k1_relat_1(sK12)),
% 7.41/1.32    inference(cnf_transformation,[],[f50])).
% 7.41/1.32  % SZS output end Proof for theBenchmark
% 7.41/1.32  % (18603)------------------------------
% 7.41/1.32  % (18603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.41/1.32  % (18603)Termination reason: Refutation
% 7.41/1.32  
% 7.41/1.32  % (18603)Memory used [KB]: 9722
% 7.41/1.32  % (18603)Time elapsed: 0.874 s
% 7.41/1.32  % (18603)------------------------------
% 7.41/1.32  % (18603)------------------------------
% 7.41/1.32  % (18566)Success in time 0.95 s
%------------------------------------------------------------------------------
