%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0591+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 177 expanded)
%              Number of leaves         :   21 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  277 ( 663 expanded)
%              Number of equality atoms :   59 ( 154 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f75,f83,f95,f124,f221,f238,f251])).

fof(f251,plain,
    ( spl9_5
    | ~ spl9_7 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl9_5
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f248,f115])).

fof(f115,plain,
    ( ~ v1_xboole_0(sK0)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl9_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f248,plain,
    ( v1_xboole_0(sK0)
    | ~ spl9_7 ),
    inference(resolution,[],[f216,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK8(X0),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK8(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f11,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f216,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl9_7
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f238,plain,
    ( spl9_2
    | spl9_8 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl9_2
    | spl9_8 ),
    inference(subsumption_resolution,[],[f236,f193])).

fof(f193,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))
    | spl9_2 ),
    inference(subsumption_resolution,[],[f192,f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f192,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1) )
    | spl9_2 ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,
    ( ! [X2,X1] :
        ( sK1 != X1
        | ~ r2_hidden(k4_tarski(X2,sK2(k2_zfmisc_1(sK0,sK1),X1)),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),X1),X1) )
    | spl9_2 ),
    inference(superposition,[],[f57,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(X3,sK2(X0,X1)),X0)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f18,f17,f16])).

fof(f16,plain,(
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

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK2(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK4(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f57,plain,
    ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl9_2
  <=> sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f236,plain,
    ( r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),sK1),sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))
    | spl9_2
    | spl9_8 ),
    inference(subsumption_resolution,[],[f233,f57])).

fof(f233,plain,
    ( sK1 = k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | r2_hidden(k4_tarski(sK3(k2_zfmisc_1(sK0,sK1),sK1),sK2(k2_zfmisc_1(sK0,sK1),sK1)),k2_zfmisc_1(sK0,sK1))
    | spl9_8 ),
    inference(resolution,[],[f220,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK3(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f220,plain,
    ( ~ r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1)
    | spl9_8 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl9_8
  <=> r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f221,plain,
    ( spl9_7
    | ~ spl9_8
    | spl9_2 ),
    inference(avatar_split_clause,[],[f209,f55,f218,f215])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k2_zfmisc_1(sK0,sK1),sK1),sK1)
        | ~ r2_hidden(X0,sK0) )
    | spl9_2 ),
    inference(resolution,[],[f193,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f124,plain,(
    ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f122,f30])).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
      | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f12])).

fof(f12,plain,
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

fof(f9,plain,(
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

fof(f122,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_5 ),
    inference(resolution,[],[f116,f44])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f116,plain,
    ( v1_xboole_0(sK0)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f95,plain,(
    ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f93,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f93,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_4 ),
    inference(resolution,[],[f92,f44])).

fof(f92,plain,
    ( v1_xboole_0(sK1)
    | ~ spl9_4 ),
    inference(resolution,[],[f74,f45])).

fof(f74,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl9_4
  <=> ! [X0] : ~ r2_hidden(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f83,plain,
    ( spl9_1
    | spl9_3 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl9_1
    | spl9_3 ),
    inference(subsumption_resolution,[],[f71,f78])).

fof(f78,plain,
    ( r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f77,f62])).

fof(f62,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,sK1))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f61,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),sK0),X0),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0) )
    | spl9_1 ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,
    ( ! [X2,X1] :
        ( sK0 != X1
        | ~ r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),X1),X2),k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),X1),X1) )
    | spl9_1 ),
    inference(superposition,[],[f53,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( k1_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK5(X0,X1),X3),X0)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f21,f24,f23,f22])).

fof(f22,plain,(
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

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK5(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK7(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f53,plain,
    ( sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl9_1
  <=> sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f77,plain,
    ( r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK6(k2_zfmisc_1(sK0,sK1),sK0)),k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0)
    | spl9_1 ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(k4_tarski(sK5(k2_zfmisc_1(sK0,sK1),X0),sK6(k2_zfmisc_1(sK0,sK1),X0)),k2_zfmisc_1(sK0,sK1))
        | r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),X0),X0) )
    | spl9_1 ),
    inference(superposition,[],[f53,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
      | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,
    ( ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl9_3
  <=> r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f75,plain,
    ( ~ spl9_3
    | spl9_4
    | spl9_1 ),
    inference(avatar_split_clause,[],[f63,f51,f73,f69])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK5(k2_zfmisc_1(sK0,sK1),sK0),sK0) )
    | spl9_1 ),
    inference(resolution,[],[f62,f43])).

fof(f58,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f32,f55,f51])).

fof(f32,plain,
    ( sK1 != k2_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
