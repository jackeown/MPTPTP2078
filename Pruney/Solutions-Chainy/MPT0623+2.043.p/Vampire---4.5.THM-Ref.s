%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:08 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 228 expanded)
%              Number of leaves         :   21 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  418 (1018 expanded)
%              Number of equality atoms :  174 ( 434 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f286,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f94,f96,f124,f137,f158,f168,f285])).

fof(f285,plain,
    ( spl8_1
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl8_1
    | ~ spl8_7 ),
    inference(trivial_inequality_removal,[],[f283])).

fof(f283,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl8_1
    | ~ spl8_7 ),
    inference(superposition,[],[f71,f229])).

fof(f229,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_7 ),
    inference(resolution,[],[f227,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f227,plain,
    ( ! [X6] :
        ( ~ r1_tarski(X6,sK0)
        | sK0 = X6 )
    | ~ spl8_7 ),
    inference(resolution,[],[f218,f169])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,sK0) )
    | ~ spl8_7 ),
    inference(resolution,[],[f136,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f136,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl8_7
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f218,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(X2,sK0),X2)
        | sK0 = X2 )
    | ~ spl8_7 ),
    inference(resolution,[],[f52,f136])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1),X1)
          | ~ r2_hidden(sK4(X0,X1),X0) )
        & ( r2_hidden(sK4(X0,X1),X1)
          | r2_hidden(sK4(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f71,plain,
    ( k1_xboole_0 != sK0
    | spl8_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl8_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f168,plain,
    ( ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(superposition,[],[f102,f75])).

fof(f75,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl8_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f102,plain,
    ( k1_xboole_0 != sK1
    | ~ spl8_3 ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 != X0 )
    | ~ spl8_3 ),
    inference(resolution,[],[f100,f61])).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( o_1_0_funct_1(X0) = k1_funct_1(sK7(X0,X1),X3)
          | ~ r2_hidden(X3,X1) )
      & k1_relat_1(sK7(X0,X1)) = X1
      & v1_funct_1(sK7(X0,X1))
      & v1_relat_1(sK7(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f19,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = o_1_0_funct_1(X0)
              | ~ r2_hidden(X3,X1) )
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( o_1_0_funct_1(X0) = k1_funct_1(sK7(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & k1_relat_1(sK7(X0,X1)) = X1
        & v1_funct_1(sK7(X0,X1))
        & v1_relat_1(sK7(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = o_1_0_funct_1(X0)
          | ~ r2_hidden(X3,X1) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = o_1_0_funct_1(X0) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).

fof(f100,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK7(X0,X1))
        | k1_xboole_0 != X1
        | sK1 != X1 )
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f99,f63])).

fof(f63,plain,(
    ! [X0,X1] : k1_relat_1(sK7(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != X1
        | ~ v1_relat_1(sK7(X0,X1))
        | sK1 != k1_relat_1(sK7(X0,X1)) )
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f97,f63])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(sK7(X0,X1))
        | ~ v1_relat_1(sK7(X0,X1))
        | sK1 != k1_relat_1(sK7(X0,X1)) )
    | ~ spl8_3 ),
    inference(resolution,[],[f89,f62])).

fof(f62,plain,(
    ! [X0,X1] : v1_funct_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != sK1 )
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl8_3
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK1
        | k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f158,plain,
    ( ~ spl8_3
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(trivial_inequality_removal,[],[f156])).

fof(f156,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(superposition,[],[f102,f138])).

fof(f138,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_6 ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0 )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_6
  <=> ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f137,plain,
    ( spl8_7
    | spl8_6
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f133,f119,f122,f135])).

fof(f119,plain,
    ( spl8_5
  <=> ! [X1] : sK5(k1_tarski(X1),sK0) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( sK1 != X0
        | ~ r2_hidden(X1,sK0)
        | k1_xboole_0 = X0 )
    | ~ spl8_5 ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( sK1 != X0
        | ~ r2_hidden(X1,sK0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X0 )
    | ~ spl8_5 ),
    inference(superposition,[],[f131,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
          & k1_relat_1(sK2(X0,X1)) = X0
          & v1_funct_1(sK2(X0,X1))
          & v1_relat_1(sK2(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f131,plain,
    ( ! [X0,X1] :
        ( sK1 != k1_relat_1(sK2(X1,X0))
        | ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = X1 )
    | ~ spl8_5 ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK0)
        | sK1 != k1_relat_1(sK2(X1,X0))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X1 )
    | ~ spl8_5 ),
    inference(resolution,[],[f129,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2(X0,X1))
        | ~ r2_hidden(X1,sK0)
        | sK1 != k1_relat_1(sK2(X0,X1))
        | k1_xboole_0 = X0 )
    | ~ spl8_5 ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( sK1 != k1_relat_1(sK2(X0,X1))
        | ~ r2_hidden(X1,sK0)
        | ~ v1_relat_1(sK2(X0,X1))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X0 )
    | ~ spl8_5 ),
    inference(resolution,[],[f127,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK2(X1,X0))
        | sK1 != k1_relat_1(sK2(X1,X0))
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(sK2(X1,X0))
        | k1_xboole_0 = X1 )
    | ~ spl8_5 ),
    inference(resolution,[],[f125,f110])).

fof(f110,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_tarski(X5),sK0)
      | sK1 != k1_relat_1(sK2(X4,X5))
      | ~ v1_funct_1(sK2(X4,X5))
      | ~ v1_relat_1(sK2(X4,X5))
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f41,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK0)
          | k1_relat_1(X2) != sK1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK0 ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f125,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tarski(X0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_5 ),
    inference(superposition,[],[f56,f120])).

fof(f120,plain,
    ( ! [X1] : sK5(k1_tarski(X1),sK0) = X1
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f124,plain,
    ( spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f117,f122,f119])).

fof(f117,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK5(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK5(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f115,f47])).

fof(f115,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X0))
      | sK5(k1_tarski(X0),sK0) = X0
      | k1_xboole_0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( sK5(k1_tarski(X0),sK0) = X0
      | sK1 != k1_relat_1(sK2(X1,X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f113,f45])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK2(X0,X1))
      | sK5(k1_tarski(X1),sK0) = X1
      | sK1 != k1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X0,X1))
      | sK5(k1_tarski(X1),sK0) = X1
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f111,f46])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK2(X1,X0))
      | sK1 != k1_relat_1(sK2(X1,X0))
      | sK5(k1_tarski(X0),sK0) = X0
      | ~ v1_relat_1(sK2(X1,X0))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f78,f110])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | sK5(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f55,f67])).

fof(f67,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | spl8_4 ),
    inference(resolution,[],[f93,f42])).

fof(f93,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl8_4
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f94,plain,
    ( spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f86,f91,f88])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f41,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f76,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f40,f73,f69])).

fof(f40,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:48:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.52  % (3524)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (3532)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (3524)Refutation not found, incomplete strategy% (3524)------------------------------
% 0.20/0.52  % (3524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3524)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (3524)Memory used [KB]: 1663
% 0.20/0.52  % (3524)Time elapsed: 0.108 s
% 0.20/0.52  % (3524)------------------------------
% 0.20/0.52  % (3524)------------------------------
% 0.20/0.52  % (3532)Refutation not found, incomplete strategy% (3532)------------------------------
% 0.20/0.52  % (3532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (3532)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (3532)Memory used [KB]: 10746
% 0.20/0.52  % (3532)Time elapsed: 0.107 s
% 0.20/0.52  % (3532)------------------------------
% 0.20/0.52  % (3532)------------------------------
% 0.20/0.52  % (3538)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (3536)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (3548)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (3540)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (3528)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (3530)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (3526)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (3527)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (3525)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (3544)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (3544)Refutation not found, incomplete strategy% (3544)------------------------------
% 0.20/0.54  % (3544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (3544)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (3544)Memory used [KB]: 10746
% 0.20/0.54  % (3544)Time elapsed: 0.137 s
% 0.20/0.54  % (3544)------------------------------
% 0.20/0.54  % (3544)------------------------------
% 0.20/0.54  % (3551)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (3539)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.54  % (3541)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.51/0.55  % (3543)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.51/0.55  % (3536)Refutation found. Thanks to Tanya!
% 1.51/0.55  % SZS status Theorem for theBenchmark
% 1.51/0.55  % SZS output start Proof for theBenchmark
% 1.51/0.55  fof(f286,plain,(
% 1.51/0.55    $false),
% 1.51/0.55    inference(avatar_sat_refutation,[],[f76,f94,f96,f124,f137,f158,f168,f285])).
% 1.51/0.55  fof(f285,plain,(
% 1.51/0.55    spl8_1 | ~spl8_7),
% 1.51/0.55    inference(avatar_contradiction_clause,[],[f284])).
% 1.51/0.55  fof(f284,plain,(
% 1.51/0.55    $false | (spl8_1 | ~spl8_7)),
% 1.51/0.55    inference(trivial_inequality_removal,[],[f283])).
% 1.51/0.55  fof(f283,plain,(
% 1.51/0.55    k1_xboole_0 != k1_xboole_0 | (spl8_1 | ~spl8_7)),
% 1.51/0.55    inference(superposition,[],[f71,f229])).
% 1.51/0.55  fof(f229,plain,(
% 1.51/0.55    k1_xboole_0 = sK0 | ~spl8_7),
% 1.51/0.55    inference(resolution,[],[f227,f42])).
% 1.51/0.55  fof(f42,plain,(
% 1.51/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.51/0.55    inference(cnf_transformation,[],[f4])).
% 1.51/0.55  fof(f4,axiom,(
% 1.51/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.51/0.55  fof(f227,plain,(
% 1.51/0.55    ( ! [X6] : (~r1_tarski(X6,sK0) | sK0 = X6) ) | ~spl8_7),
% 1.51/0.55    inference(resolution,[],[f218,f169])).
% 1.51/0.55  fof(f169,plain,(
% 1.51/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,sK0)) ) | ~spl8_7),
% 1.51/0.55    inference(resolution,[],[f136,f54])).
% 1.51/0.55  fof(f54,plain,(
% 1.51/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.51/0.55    inference(cnf_transformation,[],[f33])).
% 1.51/0.55  fof(f33,plain,(
% 1.51/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 1.51/0.55  fof(f32,plain,(
% 1.51/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.51/0.55    introduced(choice_axiom,[])).
% 1.51/0.55  fof(f31,plain,(
% 1.51/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.55    inference(rectify,[],[f30])).
% 1.51/0.55  fof(f30,plain,(
% 1.51/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.51/0.55    inference(nnf_transformation,[],[f18])).
% 1.51/0.55  fof(f18,plain,(
% 1.51/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.51/0.55    inference(ennf_transformation,[],[f1])).
% 1.51/0.55  fof(f1,axiom,(
% 1.51/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.51/0.55  fof(f136,plain,(
% 1.51/0.55    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl8_7),
% 1.51/0.55    inference(avatar_component_clause,[],[f135])).
% 1.51/0.55  fof(f135,plain,(
% 1.51/0.55    spl8_7 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 1.51/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.51/0.55  fof(f218,plain,(
% 1.51/0.55    ( ! [X2] : (r2_hidden(sK4(X2,sK0),X2) | sK0 = X2) ) | ~spl8_7),
% 1.51/0.55    inference(resolution,[],[f52,f136])).
% 1.51/0.55  fof(f52,plain,(
% 1.51/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | X0 = X1 | r2_hidden(sK4(X0,X1),X0)) )),
% 1.51/0.55    inference(cnf_transformation,[],[f29])).
% 1.51/0.55  fof(f29,plain,(
% 1.51/0.55    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 1.51/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f28])).
% 1.51/0.55  fof(f28,plain,(
% 1.51/0.55    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0)) & (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0))))),
% 1.51/0.55    introduced(choice_axiom,[])).
% 1.51/0.55  fof(f27,plain,(
% 1.51/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.51/0.55    inference(nnf_transformation,[],[f17])).
% 1.51/0.55  fof(f17,plain,(
% 1.51/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.51/0.55    inference(ennf_transformation,[],[f2])).
% 1.51/0.55  fof(f2,axiom,(
% 1.51/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.51/0.55  fof(f71,plain,(
% 1.51/0.55    k1_xboole_0 != sK0 | spl8_1),
% 1.51/0.55    inference(avatar_component_clause,[],[f69])).
% 1.51/0.55  fof(f69,plain,(
% 1.51/0.55    spl8_1 <=> k1_xboole_0 = sK0),
% 1.51/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.51/0.55  fof(f168,plain,(
% 1.51/0.55    ~spl8_2 | ~spl8_3),
% 1.51/0.55    inference(avatar_contradiction_clause,[],[f167])).
% 1.51/0.55  fof(f167,plain,(
% 1.51/0.55    $false | (~spl8_2 | ~spl8_3)),
% 1.51/0.55    inference(trivial_inequality_removal,[],[f164])).
% 1.51/0.55  fof(f164,plain,(
% 1.51/0.55    k1_xboole_0 != k1_xboole_0 | (~spl8_2 | ~spl8_3)),
% 1.51/0.55    inference(superposition,[],[f102,f75])).
% 1.51/0.55  fof(f75,plain,(
% 1.51/0.55    k1_xboole_0 = sK1 | ~spl8_2),
% 1.51/0.55    inference(avatar_component_clause,[],[f73])).
% 1.51/0.55  fof(f73,plain,(
% 1.51/0.55    spl8_2 <=> k1_xboole_0 = sK1),
% 1.51/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.51/0.55  fof(f102,plain,(
% 1.51/0.55    k1_xboole_0 != sK1 | ~spl8_3),
% 1.51/0.55    inference(equality_resolution,[],[f101])).
% 1.51/0.55  fof(f101,plain,(
% 1.51/0.55    ( ! [X0] : (sK1 != X0 | k1_xboole_0 != X0) ) | ~spl8_3),
% 1.51/0.55    inference(resolution,[],[f100,f61])).
% 1.51/0.55  fof(f61,plain,(
% 1.51/0.55    ( ! [X0,X1] : (v1_relat_1(sK7(X0,X1))) )),
% 1.51/0.55    inference(cnf_transformation,[],[f39])).
% 1.51/0.55  fof(f39,plain,(
% 1.51/0.55    ! [X0,X1] : (! [X3] : (o_1_0_funct_1(X0) = k1_funct_1(sK7(X0,X1),X3) | ~r2_hidden(X3,X1)) & k1_relat_1(sK7(X0,X1)) = X1 & v1_funct_1(sK7(X0,X1)) & v1_relat_1(sK7(X0,X1)))),
% 1.51/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f19,f38])).
% 1.51/0.55  fof(f38,plain,(
% 1.51/0.55    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = o_1_0_funct_1(X0) | ~r2_hidden(X3,X1)) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (o_1_0_funct_1(X0) = k1_funct_1(sK7(X0,X1),X3) | ~r2_hidden(X3,X1)) & k1_relat_1(sK7(X0,X1)) = X1 & v1_funct_1(sK7(X0,X1)) & v1_relat_1(sK7(X0,X1))))),
% 1.51/0.55    introduced(choice_axiom,[])).
% 1.51/0.55  fof(f19,plain,(
% 1.51/0.55    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = o_1_0_funct_1(X0) | ~r2_hidden(X3,X1)) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.51/0.55    inference(ennf_transformation,[],[f7])).
% 1.51/0.55  fof(f7,axiom,(
% 1.51/0.55    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X1) => k1_funct_1(X2,X3) = o_1_0_funct_1(X0)) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).
% 1.51/0.55  fof(f100,plain,(
% 1.51/0.55    ( ! [X0,X1] : (~v1_relat_1(sK7(X0,X1)) | k1_xboole_0 != X1 | sK1 != X1) ) | ~spl8_3),
% 1.51/0.55    inference(forward_demodulation,[],[f99,f63])).
% 1.51/0.55  fof(f63,plain,(
% 1.51/0.55    ( ! [X0,X1] : (k1_relat_1(sK7(X0,X1)) = X1) )),
% 1.51/0.55    inference(cnf_transformation,[],[f39])).
% 1.51/0.55  fof(f99,plain,(
% 1.51/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | ~v1_relat_1(sK7(X0,X1)) | sK1 != k1_relat_1(sK7(X0,X1))) ) | ~spl8_3),
% 1.51/0.55    inference(forward_demodulation,[],[f97,f63])).
% 1.51/0.55  fof(f97,plain,(
% 1.51/0.55    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(sK7(X0,X1)) | ~v1_relat_1(sK7(X0,X1)) | sK1 != k1_relat_1(sK7(X0,X1))) ) | ~spl8_3),
% 1.51/0.55    inference(resolution,[],[f89,f62])).
% 1.51/0.55  fof(f62,plain,(
% 1.51/0.55    ( ! [X0,X1] : (v1_funct_1(sK7(X0,X1))) )),
% 1.51/0.55    inference(cnf_transformation,[],[f39])).
% 1.51/0.55  fof(f89,plain,(
% 1.51/0.55    ( ! [X0] : (~v1_funct_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != sK1) ) | ~spl8_3),
% 1.51/0.55    inference(avatar_component_clause,[],[f88])).
% 1.51/0.55  fof(f88,plain,(
% 1.51/0.55    spl8_3 <=> ! [X0] : (k1_relat_1(X0) != sK1 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0))),
% 1.51/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.51/0.55  fof(f158,plain,(
% 1.51/0.55    ~spl8_3 | ~spl8_6),
% 1.51/0.55    inference(avatar_contradiction_clause,[],[f157])).
% 1.51/0.55  fof(f157,plain,(
% 1.51/0.55    $false | (~spl8_3 | ~spl8_6)),
% 1.51/0.55    inference(trivial_inequality_removal,[],[f156])).
% 1.51/0.55  fof(f156,plain,(
% 1.51/0.55    k1_xboole_0 != k1_xboole_0 | (~spl8_3 | ~spl8_6)),
% 1.51/0.55    inference(superposition,[],[f102,f138])).
% 1.51/0.55  fof(f138,plain,(
% 1.51/0.55    k1_xboole_0 = sK1 | ~spl8_6),
% 1.51/0.55    inference(equality_resolution,[],[f123])).
% 1.51/0.55  fof(f123,plain,(
% 1.51/0.55    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = X0) ) | ~spl8_6),
% 1.51/0.55    inference(avatar_component_clause,[],[f122])).
% 1.51/0.55  fof(f122,plain,(
% 1.51/0.55    spl8_6 <=> ! [X0] : (sK1 != X0 | k1_xboole_0 = X0)),
% 1.51/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.51/0.55  fof(f137,plain,(
% 1.51/0.55    spl8_7 | spl8_6 | ~spl8_5),
% 1.51/0.55    inference(avatar_split_clause,[],[f133,f119,f122,f135])).
% 1.51/0.55  fof(f119,plain,(
% 1.51/0.55    spl8_5 <=> ! [X1] : sK5(k1_tarski(X1),sK0) = X1),
% 1.51/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.51/0.55  fof(f133,plain,(
% 1.51/0.55    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0) ) | ~spl8_5),
% 1.51/0.55    inference(duplicate_literal_removal,[],[f132])).
% 1.51/0.55  fof(f132,plain,(
% 1.51/0.55    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0 | k1_xboole_0 = X0) ) | ~spl8_5),
% 1.51/0.55    inference(superposition,[],[f131,f47])).
% 1.51/0.55  fof(f47,plain,(
% 1.51/0.55    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.51/0.55    inference(cnf_transformation,[],[f24])).
% 1.51/0.55  fof(f24,plain,(
% 1.51/0.55    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 1.51/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f23])).
% 1.51/0.55  fof(f23,plain,(
% 1.51/0.55    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 1.51/0.55    introduced(choice_axiom,[])).
% 1.51/0.55  fof(f15,plain,(
% 1.51/0.55    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.51/0.55    inference(ennf_transformation,[],[f8])).
% 1.51/0.55  fof(f8,axiom,(
% 1.51/0.55    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 1.51/0.55  fof(f131,plain,(
% 1.51/0.55    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | ~r2_hidden(X0,sK0) | k1_xboole_0 = X1) ) | ~spl8_5),
% 1.51/0.55    inference(duplicate_literal_removal,[],[f130])).
% 1.51/0.55  fof(f130,plain,(
% 1.51/0.55    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | sK1 != k1_relat_1(sK2(X1,X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X1) ) | ~spl8_5),
% 1.51/0.55    inference(resolution,[],[f129,f45])).
% 1.51/0.55  fof(f45,plain,(
% 1.51/0.55    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.51/0.55    inference(cnf_transformation,[],[f24])).
% 1.51/0.55  fof(f129,plain,(
% 1.51/0.55    ( ! [X0,X1] : (~v1_relat_1(sK2(X0,X1)) | ~r2_hidden(X1,sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) ) | ~spl8_5),
% 1.51/0.55    inference(duplicate_literal_removal,[],[f128])).
% 1.51/0.55  fof(f128,plain,(
% 1.51/0.55    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X0,X1)) | ~r2_hidden(X1,sK0) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X0) ) | ~spl8_5),
% 1.51/0.55    inference(resolution,[],[f127,f46])).
% 1.51/0.55  fof(f46,plain,(
% 1.51/0.55    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.51/0.55    inference(cnf_transformation,[],[f24])).
% 1.51/0.55  fof(f127,plain,(
% 1.51/0.55    ( ! [X0,X1] : (~v1_funct_1(sK2(X1,X0)) | sK1 != k1_relat_1(sK2(X1,X0)) | ~r2_hidden(X0,sK0) | ~v1_relat_1(sK2(X1,X0)) | k1_xboole_0 = X1) ) | ~spl8_5),
% 1.51/0.55    inference(resolution,[],[f125,f110])).
% 1.51/0.55  fof(f110,plain,(
% 1.51/0.55    ( ! [X4,X5] : (~r1_tarski(k1_tarski(X5),sK0) | sK1 != k1_relat_1(sK2(X4,X5)) | ~v1_funct_1(sK2(X4,X5)) | ~v1_relat_1(sK2(X4,X5)) | k1_xboole_0 = X4) )),
% 1.51/0.55    inference(superposition,[],[f41,f48])).
% 1.51/0.55  fof(f48,plain,(
% 1.51/0.55    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.51/0.55    inference(cnf_transformation,[],[f24])).
% 1.51/0.55  fof(f41,plain,(
% 1.51/0.55    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.51/0.55    inference(cnf_transformation,[],[f21])).
% 1.51/0.55  fof(f21,plain,(
% 1.51/0.55    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 1.51/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).
% 1.51/0.55  fof(f20,plain,(
% 1.51/0.55    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 1.51/0.55    introduced(choice_axiom,[])).
% 1.51/0.55  fof(f13,plain,(
% 1.51/0.55    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.51/0.55    inference(flattening,[],[f12])).
% 1.51/0.55  fof(f12,plain,(
% 1.51/0.55    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.51/0.55    inference(ennf_transformation,[],[f10])).
% 1.51/0.55  fof(f10,negated_conjecture,(
% 1.51/0.55    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.51/0.55    inference(negated_conjecture,[],[f9])).
% 1.51/0.55  fof(f9,conjecture,(
% 1.51/0.55    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 1.51/0.55  fof(f125,plain,(
% 1.51/0.55    ( ! [X0] : (r1_tarski(k1_tarski(X0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl8_5),
% 1.51/0.55    inference(superposition,[],[f56,f120])).
% 1.51/0.55  fof(f120,plain,(
% 1.51/0.55    ( ! [X1] : (sK5(k1_tarski(X1),sK0) = X1) ) | ~spl8_5),
% 1.51/0.55    inference(avatar_component_clause,[],[f119])).
% 1.51/0.55  fof(f56,plain,(
% 1.51/0.55    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.51/0.55    inference(cnf_transformation,[],[f33])).
% 1.51/0.55  fof(f124,plain,(
% 1.51/0.55    spl8_5 | spl8_6),
% 1.51/0.55    inference(avatar_split_clause,[],[f117,f122,f119])).
% 1.51/0.55  fof(f117,plain,(
% 1.51/0.55    ( ! [X0,X1] : (sK1 != X0 | sK5(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0) )),
% 1.51/0.55    inference(duplicate_literal_removal,[],[f116])).
% 1.51/0.55  fof(f116,plain,(
% 1.51/0.55    ( ! [X0,X1] : (sK1 != X0 | sK5(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.51/0.55    inference(superposition,[],[f115,f47])).
% 1.51/0.55  fof(f115,plain,(
% 1.51/0.55    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | sK5(k1_tarski(X0),sK0) = X0 | k1_xboole_0 = X1) )),
% 1.51/0.55    inference(duplicate_literal_removal,[],[f114])).
% 1.51/0.55  fof(f114,plain,(
% 1.51/0.55    ( ! [X0,X1] : (sK5(k1_tarski(X0),sK0) = X0 | sK1 != k1_relat_1(sK2(X1,X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X1) )),
% 1.51/0.55    inference(resolution,[],[f113,f45])).
% 1.51/0.55  fof(f113,plain,(
% 1.51/0.55    ( ! [X0,X1] : (~v1_relat_1(sK2(X0,X1)) | sK5(k1_tarski(X1),sK0) = X1 | sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.51/0.55    inference(duplicate_literal_removal,[],[f112])).
% 1.51/0.55  fof(f112,plain,(
% 1.51/0.55    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X0,X1)) | sK5(k1_tarski(X1),sK0) = X1 | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.51/0.55    inference(resolution,[],[f111,f46])).
% 1.51/0.55  fof(f111,plain,(
% 1.51/0.55    ( ! [X0,X1] : (~v1_funct_1(sK2(X1,X0)) | sK1 != k1_relat_1(sK2(X1,X0)) | sK5(k1_tarski(X0),sK0) = X0 | ~v1_relat_1(sK2(X1,X0)) | k1_xboole_0 = X1) )),
% 1.51/0.55    inference(resolution,[],[f78,f110])).
% 1.51/0.55  fof(f78,plain,(
% 1.51/0.55    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | sK5(k1_tarski(X0),X1) = X0) )),
% 1.51/0.55    inference(resolution,[],[f55,f67])).
% 1.51/0.55  fof(f67,plain,(
% 1.51/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.51/0.55    inference(equality_resolution,[],[f57])).
% 1.51/0.55  fof(f57,plain,(
% 1.51/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.51/0.55    inference(cnf_transformation,[],[f37])).
% 1.51/0.55  fof(f37,plain,(
% 1.51/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.51/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f36])).
% 1.51/0.55  fof(f36,plain,(
% 1.51/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 1.51/0.55    introduced(choice_axiom,[])).
% 1.51/0.55  fof(f35,plain,(
% 1.51/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.51/0.55    inference(rectify,[],[f34])).
% 1.51/0.55  fof(f34,plain,(
% 1.51/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.51/0.55    inference(nnf_transformation,[],[f5])).
% 1.51/0.55  fof(f5,axiom,(
% 1.51/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.51/0.55  fof(f55,plain,(
% 1.51/0.55    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.51/0.55    inference(cnf_transformation,[],[f33])).
% 1.51/0.55  fof(f96,plain,(
% 1.51/0.55    spl8_4),
% 1.51/0.55    inference(avatar_contradiction_clause,[],[f95])).
% 1.51/0.55  fof(f95,plain,(
% 1.51/0.55    $false | spl8_4),
% 1.51/0.55    inference(resolution,[],[f93,f42])).
% 1.51/0.55  fof(f93,plain,(
% 1.51/0.55    ~r1_tarski(k1_xboole_0,sK0) | spl8_4),
% 1.51/0.55    inference(avatar_component_clause,[],[f91])).
% 1.51/0.55  fof(f91,plain,(
% 1.51/0.55    spl8_4 <=> r1_tarski(k1_xboole_0,sK0)),
% 1.51/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.51/0.55  fof(f94,plain,(
% 1.51/0.55    spl8_3 | ~spl8_4),
% 1.51/0.55    inference(avatar_split_clause,[],[f86,f91,f88])).
% 1.51/0.55  fof(f86,plain,(
% 1.51/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 1.51/0.55    inference(duplicate_literal_removal,[],[f85])).
% 1.51/0.55  fof(f85,plain,(
% 1.51/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.55    inference(superposition,[],[f41,f43])).
% 1.51/0.55  fof(f43,plain,(
% 1.51/0.55    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.51/0.55    inference(cnf_transformation,[],[f22])).
% 1.51/0.55  fof(f22,plain,(
% 1.51/0.55    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.51/0.55    inference(nnf_transformation,[],[f14])).
% 1.51/0.55  fof(f14,plain,(
% 1.51/0.55    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.51/0.55    inference(ennf_transformation,[],[f6])).
% 1.51/0.55  fof(f6,axiom,(
% 1.51/0.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.51/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 1.51/0.55  fof(f76,plain,(
% 1.51/0.55    ~spl8_1 | spl8_2),
% 1.51/0.55    inference(avatar_split_clause,[],[f40,f73,f69])).
% 1.51/0.55  fof(f40,plain,(
% 1.51/0.55    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 1.51/0.55    inference(cnf_transformation,[],[f21])).
% 1.51/0.55  % SZS output end Proof for theBenchmark
% 1.51/0.55  % (3536)------------------------------
% 1.51/0.55  % (3536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (3536)Termination reason: Refutation
% 1.51/0.55  
% 1.51/0.55  % (3536)Memory used [KB]: 6268
% 1.51/0.55  % (3536)Time elapsed: 0.131 s
% 1.51/0.55  % (3536)------------------------------
% 1.51/0.55  % (3536)------------------------------
% 1.51/0.55  % (3523)Success in time 0.193 s
%------------------------------------------------------------------------------
