%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:02 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 146 expanded)
%              Number of leaves         :   27 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  297 ( 508 expanded)
%              Number of equality atoms :   93 ( 195 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f210,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f73,f77,f90,f148,f169,f172,f175,f177,f209])).

fof(f209,plain,
    ( spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f208,f143,f71,f67,f60])).

fof(f60,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f67,plain,
    ( spl7_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f71,plain,
    ( spl7_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f143,plain,
    ( spl7_9
  <=> ! [X1] :
        ( sK0 = k2_relat_1(X1)
        | r2_hidden(k4_tarski(sK5(X1,sK0),sK4(X1,sK0)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f208,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f206,f72])).

fof(f72,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f206,plain,
    ( k2_relat_1(k1_xboole_0) = sK0
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(resolution,[],[f151,f68])).

fof(f68,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f151,plain,
    ( ! [X3] :
        ( ~ v1_xboole_0(X3)
        | sK0 = k2_relat_1(X3) )
    | ~ spl7_9 ),
    inference(resolution,[],[f144,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f144,plain,
    ( ! [X1] :
        ( r2_hidden(k4_tarski(sK5(X1,sK0),sK4(X1,sK0)),X1)
        | sK0 = k2_relat_1(X1) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f143])).

fof(f177,plain,
    ( ~ spl7_3
    | spl7_7 ),
    inference(avatar_split_clause,[],[f176,f84,f67])).

fof(f84,plain,
    ( spl7_7
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f176,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_7 ),
    inference(resolution,[],[f85,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f85,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f84])).

fof(f175,plain,
    ( ~ spl7_3
    | spl7_6 ),
    inference(avatar_split_clause,[],[f173,f81,f67])).

fof(f81,plain,
    ( spl7_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f173,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_6 ),
    inference(resolution,[],[f82,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f82,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f172,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | spl7_8 ),
    inference(resolution,[],[f88,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f88,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl7_8
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f169,plain,
    ( spl7_2
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f168,f146,f63])).

fof(f63,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f146,plain,
    ( spl7_10
  <=> ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f168,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_10 ),
    inference(equality_resolution,[],[f147])).

fof(f147,plain,
    ( ! [X0] :
        ( sK1 != X0
        | k1_xboole_0 = X0 )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f146])).

fof(f148,plain,
    ( spl7_9
    | spl7_10 ),
    inference(avatar_split_clause,[],[f141,f146,f143])).

fof(f141,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK0 = k2_relat_1(X1)
      | k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK5(X1,sK0),sK4(X1,sK0)),X1) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK0 = k2_relat_1(X1)
      | k1_xboole_0 = X0
      | r2_hidden(k4_tarski(sK5(X1,sK0),sK4(X1,sK0)),X1)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f138,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
          & k1_relat_1(sK2(X0,X1)) = X0
          & v1_funct_1(sK2(X0,X1))
          & v1_relat_1(sK2(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f20])).

fof(f20,plain,(
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

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f138,plain,(
    ! [X12,X11] :
      ( sK1 != k1_relat_1(sK2(X12,sK4(X11,sK0)))
      | sK0 = k2_relat_1(X11)
      | k1_xboole_0 = X12
      | r2_hidden(k4_tarski(sK5(X11,sK0),sK4(X11,sK0)),X11) ) ),
    inference(resolution,[],[f50,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = X0
      | sK1 != k1_relat_1(sK2(X0,X1)) ) ),
    inference(resolution,[],[f96,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f39])).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_tarski(X1,X1),sK0)
      | sK1 != k1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(global_subsumption,[],[f43,f42,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_tarski(X1,X1),sK0)
      | sK1 != k1_relat_1(sK2(X0,X1))
      | ~ v1_funct_1(sK2(X0,X1))
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f34,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(sK2(X0,X1)) = k2_tarski(X1,X1)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f39])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f18])).

fof(f18,plain,
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

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK6(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f27,f30,f29,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f90,plain,
    ( ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f79,f75,f71,f63,f87,f84,f81])).

fof(f75,plain,
    ( spl7_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f79,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f78,f76])).

fof(f76,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f78,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | k1_relat_1(k1_xboole_0) != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_4 ),
    inference(superposition,[],[f34,f72])).

fof(f77,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f36,f75])).

fof(f36,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f73,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f37,f71])).

fof(f37,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f69,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f35,f67])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f65,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f33,f63,f60])).

fof(f33,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:26:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (20276)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % (20295)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.50  % (20287)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.23/0.51  % (20305)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.23/0.51  % (20288)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.51  % (20289)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.23/0.52  % (20283)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.23/0.52  % (20277)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.23/0.52  % (20296)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.23/0.52  % (20276)Refutation not found, incomplete strategy% (20276)------------------------------
% 1.23/0.52  % (20276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (20287)Refutation not found, incomplete strategy% (20287)------------------------------
% 1.23/0.52  % (20287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (20287)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.52  
% 1.23/0.52  % (20287)Memory used [KB]: 10746
% 1.23/0.52  % (20287)Time elapsed: 0.115 s
% 1.23/0.52  % (20287)------------------------------
% 1.23/0.52  % (20287)------------------------------
% 1.23/0.52  % (20303)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.23/0.52  % (20295)Refutation found. Thanks to Tanya!
% 1.23/0.52  % SZS status Theorem for theBenchmark
% 1.23/0.52  % SZS output start Proof for theBenchmark
% 1.23/0.52  fof(f210,plain,(
% 1.23/0.52    $false),
% 1.23/0.52    inference(avatar_sat_refutation,[],[f65,f69,f73,f77,f90,f148,f169,f172,f175,f177,f209])).
% 1.23/0.52  fof(f209,plain,(
% 1.23/0.52    spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_9),
% 1.23/0.52    inference(avatar_split_clause,[],[f208,f143,f71,f67,f60])).
% 1.23/0.52  fof(f60,plain,(
% 1.23/0.52    spl7_1 <=> k1_xboole_0 = sK0),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.23/0.52  fof(f67,plain,(
% 1.23/0.52    spl7_3 <=> v1_xboole_0(k1_xboole_0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.23/0.52  fof(f71,plain,(
% 1.23/0.52    spl7_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.23/0.52  fof(f143,plain,(
% 1.23/0.52    spl7_9 <=> ! [X1] : (sK0 = k2_relat_1(X1) | r2_hidden(k4_tarski(sK5(X1,sK0),sK4(X1,sK0)),X1))),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.23/0.52  fof(f208,plain,(
% 1.23/0.52    k1_xboole_0 = sK0 | (~spl7_3 | ~spl7_4 | ~spl7_9)),
% 1.23/0.52    inference(forward_demodulation,[],[f206,f72])).
% 1.23/0.52  fof(f72,plain,(
% 1.23/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl7_4),
% 1.23/0.52    inference(avatar_component_clause,[],[f71])).
% 1.23/0.52  fof(f206,plain,(
% 1.23/0.52    k2_relat_1(k1_xboole_0) = sK0 | (~spl7_3 | ~spl7_9)),
% 1.23/0.52    inference(resolution,[],[f151,f68])).
% 1.23/0.52  fof(f68,plain,(
% 1.23/0.52    v1_xboole_0(k1_xboole_0) | ~spl7_3),
% 1.23/0.52    inference(avatar_component_clause,[],[f67])).
% 1.23/0.52  fof(f151,plain,(
% 1.23/0.52    ( ! [X3] : (~v1_xboole_0(X3) | sK0 = k2_relat_1(X3)) ) | ~spl7_9),
% 1.23/0.52    inference(resolution,[],[f144,f46])).
% 1.23/0.52  fof(f46,plain,(
% 1.23/0.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f25])).
% 1.23/0.52  fof(f25,plain,(
% 1.23/0.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 1.23/0.52  fof(f24,plain,(
% 1.23/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f23,plain,(
% 1.23/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.23/0.52    inference(rectify,[],[f22])).
% 1.23/0.52  fof(f22,plain,(
% 1.23/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.23/0.52    inference(nnf_transformation,[],[f1])).
% 1.23/0.52  fof(f1,axiom,(
% 1.23/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.23/0.52  fof(f144,plain,(
% 1.23/0.52    ( ! [X1] : (r2_hidden(k4_tarski(sK5(X1,sK0),sK4(X1,sK0)),X1) | sK0 = k2_relat_1(X1)) ) | ~spl7_9),
% 1.23/0.52    inference(avatar_component_clause,[],[f143])).
% 1.23/0.52  fof(f177,plain,(
% 1.23/0.52    ~spl7_3 | spl7_7),
% 1.23/0.52    inference(avatar_split_clause,[],[f176,f84,f67])).
% 1.23/0.52  fof(f84,plain,(
% 1.23/0.52    spl7_7 <=> v1_funct_1(k1_xboole_0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.23/0.52  fof(f176,plain,(
% 1.23/0.52    ~v1_xboole_0(k1_xboole_0) | spl7_7),
% 1.23/0.52    inference(resolution,[],[f85,f40])).
% 1.23/0.52  fof(f40,plain,(
% 1.23/0.52    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f15])).
% 1.23/0.52  fof(f15,plain,(
% 1.23/0.52    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 1.23/0.52    inference(ennf_transformation,[],[f9])).
% 1.23/0.52  fof(f9,axiom,(
% 1.23/0.52    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 1.23/0.52  fof(f85,plain,(
% 1.23/0.52    ~v1_funct_1(k1_xboole_0) | spl7_7),
% 1.23/0.52    inference(avatar_component_clause,[],[f84])).
% 1.23/0.52  fof(f175,plain,(
% 1.23/0.52    ~spl7_3 | spl7_6),
% 1.23/0.52    inference(avatar_split_clause,[],[f173,f81,f67])).
% 1.23/0.52  fof(f81,plain,(
% 1.23/0.52    spl7_6 <=> v1_relat_1(k1_xboole_0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.23/0.52  fof(f173,plain,(
% 1.23/0.52    ~v1_xboole_0(k1_xboole_0) | spl7_6),
% 1.23/0.52    inference(resolution,[],[f82,f41])).
% 1.23/0.52  fof(f41,plain,(
% 1.23/0.52    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f16])).
% 1.23/0.52  fof(f16,plain,(
% 1.23/0.52    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.23/0.52    inference(ennf_transformation,[],[f6])).
% 1.23/0.52  fof(f6,axiom,(
% 1.23/0.52    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.23/0.52  fof(f82,plain,(
% 1.23/0.52    ~v1_relat_1(k1_xboole_0) | spl7_6),
% 1.23/0.52    inference(avatar_component_clause,[],[f81])).
% 1.23/0.52  fof(f172,plain,(
% 1.23/0.52    spl7_8),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f171])).
% 1.23/0.52  fof(f171,plain,(
% 1.23/0.52    $false | spl7_8),
% 1.23/0.52    inference(resolution,[],[f88,f38])).
% 1.23/0.52  fof(f38,plain,(
% 1.23/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f3])).
% 1.23/0.52  fof(f3,axiom,(
% 1.23/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.23/0.52  fof(f88,plain,(
% 1.23/0.52    ~r1_tarski(k1_xboole_0,sK0) | spl7_8),
% 1.23/0.52    inference(avatar_component_clause,[],[f87])).
% 1.23/0.52  fof(f87,plain,(
% 1.23/0.52    spl7_8 <=> r1_tarski(k1_xboole_0,sK0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.23/0.52  fof(f169,plain,(
% 1.23/0.52    spl7_2 | ~spl7_10),
% 1.23/0.52    inference(avatar_split_clause,[],[f168,f146,f63])).
% 1.23/0.52  fof(f63,plain,(
% 1.23/0.52    spl7_2 <=> k1_xboole_0 = sK1),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.23/0.52  fof(f146,plain,(
% 1.23/0.52    spl7_10 <=> ! [X0] : (sK1 != X0 | k1_xboole_0 = X0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.23/0.52  fof(f168,plain,(
% 1.23/0.52    k1_xboole_0 = sK1 | ~spl7_10),
% 1.23/0.52    inference(equality_resolution,[],[f147])).
% 1.23/0.52  fof(f147,plain,(
% 1.23/0.52    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = X0) ) | ~spl7_10),
% 1.23/0.52    inference(avatar_component_clause,[],[f146])).
% 1.23/0.52  fof(f148,plain,(
% 1.23/0.52    spl7_9 | spl7_10),
% 1.23/0.52    inference(avatar_split_clause,[],[f141,f146,f143])).
% 1.23/0.52  fof(f141,plain,(
% 1.23/0.52    ( ! [X0,X1] : (sK1 != X0 | sK0 = k2_relat_1(X1) | k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK5(X1,sK0),sK4(X1,sK0)),X1)) )),
% 1.23/0.52    inference(duplicate_literal_removal,[],[f140])).
% 1.23/0.52  fof(f140,plain,(
% 1.23/0.52    ( ! [X0,X1] : (sK1 != X0 | sK0 = k2_relat_1(X1) | k1_xboole_0 = X0 | r2_hidden(k4_tarski(sK5(X1,sK0),sK4(X1,sK0)),X1) | k1_xboole_0 = X0) )),
% 1.23/0.52    inference(superposition,[],[f138,f44])).
% 1.23/0.52  fof(f44,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.23/0.52    inference(cnf_transformation,[],[f21])).
% 1.23/0.52  fof(f21,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 1.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f20])).
% 1.23/0.52  fof(f20,plain,(
% 1.23/0.52    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f17,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.23/0.52    inference(ennf_transformation,[],[f10])).
% 1.23/0.52  fof(f10,axiom,(
% 1.23/0.52    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.23/0.52  fof(f138,plain,(
% 1.23/0.52    ( ! [X12,X11] : (sK1 != k1_relat_1(sK2(X12,sK4(X11,sK0))) | sK0 = k2_relat_1(X11) | k1_xboole_0 = X12 | r2_hidden(k4_tarski(sK5(X11,sK0),sK4(X11,sK0)),X11)) )),
% 1.23/0.52    inference(resolution,[],[f50,f97])).
% 1.23/0.52  fof(f97,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | k1_xboole_0 = X0 | sK1 != k1_relat_1(sK2(X0,X1))) )),
% 1.23/0.52    inference(resolution,[],[f96,f55])).
% 1.23/0.52  fof(f55,plain,(
% 1.23/0.52    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.23/0.52    inference(definition_unfolding,[],[f53,f39])).
% 1.23/0.52  fof(f39,plain,(
% 1.23/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f4])).
% 1.23/0.52  fof(f4,axiom,(
% 1.23/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.23/0.52  fof(f53,plain,(
% 1.23/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f32])).
% 1.23/0.52  fof(f32,plain,(
% 1.23/0.52    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.23/0.52    inference(nnf_transformation,[],[f5])).
% 1.23/0.52  fof(f5,axiom,(
% 1.23/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.23/0.52  fof(f96,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~r1_tarski(k2_tarski(X1,X1),sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.23/0.52    inference(global_subsumption,[],[f43,f42,f93])).
% 1.23/0.52  fof(f93,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~r1_tarski(k2_tarski(X1,X1),sK0) | sK1 != k1_relat_1(sK2(X0,X1)) | ~v1_funct_1(sK2(X0,X1)) | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.23/0.52    inference(superposition,[],[f34,f54])).
% 1.23/0.52  fof(f54,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k2_relat_1(sK2(X0,X1)) = k2_tarski(X1,X1) | k1_xboole_0 = X0) )),
% 1.23/0.52    inference(definition_unfolding,[],[f45,f39])).
% 1.23/0.52  fof(f45,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.23/0.52    inference(cnf_transformation,[],[f21])).
% 1.23/0.52  fof(f34,plain,(
% 1.23/0.52    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  fof(f19,plain,(
% 1.23/0.52    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 1.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f18])).
% 1.23/0.52  fof(f18,plain,(
% 1.23/0.52    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f14,plain,(
% 1.23/0.52    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.23/0.52    inference(flattening,[],[f13])).
% 1.23/0.52  fof(f13,plain,(
% 1.23/0.52    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.23/0.52    inference(ennf_transformation,[],[f12])).
% 1.23/0.52  fof(f12,negated_conjecture,(
% 1.23/0.52    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.23/0.52    inference(negated_conjecture,[],[f11])).
% 1.23/0.52  fof(f11,conjecture,(
% 1.23/0.52    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 1.23/0.52  fof(f42,plain,(
% 1.23/0.52    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.23/0.52    inference(cnf_transformation,[],[f21])).
% 1.23/0.52  fof(f43,plain,(
% 1.23/0.52    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.23/0.52    inference(cnf_transformation,[],[f21])).
% 1.23/0.52  fof(f50,plain,(
% 1.23/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | k2_relat_1(X0) = X1) )),
% 1.23/0.52    inference(cnf_transformation,[],[f31])).
% 1.23/0.52  fof(f31,plain,(
% 1.23/0.52    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK6(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f27,f30,f29,f28])).
% 1.23/0.52  fof(f28,plain,(
% 1.23/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK4(X0,X1)),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f29,plain,(
% 1.23/0.52    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK4(X0,X1)),X0) => r2_hidden(k4_tarski(sK5(X0,X1),sK4(X0,X1)),X0))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f30,plain,(
% 1.23/0.52    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK6(X0,X5),X5),X0))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f27,plain,(
% 1.23/0.52    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 1.23/0.52    inference(rectify,[],[f26])).
% 1.23/0.52  fof(f26,plain,(
% 1.23/0.52    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 1.23/0.52    inference(nnf_transformation,[],[f7])).
% 1.23/0.52  fof(f7,axiom,(
% 1.23/0.52    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.23/0.52  fof(f90,plain,(
% 1.23/0.52    ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_2 | ~spl7_4 | ~spl7_5),
% 1.23/0.52    inference(avatar_split_clause,[],[f79,f75,f71,f63,f87,f84,f81])).
% 1.23/0.52  fof(f75,plain,(
% 1.23/0.52    spl7_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.23/0.52  fof(f79,plain,(
% 1.23/0.52    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | (~spl7_4 | ~spl7_5)),
% 1.23/0.52    inference(forward_demodulation,[],[f78,f76])).
% 1.23/0.52  fof(f76,plain,(
% 1.23/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_5),
% 1.23/0.52    inference(avatar_component_clause,[],[f75])).
% 1.23/0.52  fof(f78,plain,(
% 1.23/0.52    ~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(k1_xboole_0) != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl7_4),
% 1.23/0.52    inference(superposition,[],[f34,f72])).
% 1.23/0.52  fof(f77,plain,(
% 1.23/0.52    spl7_5),
% 1.23/0.52    inference(avatar_split_clause,[],[f36,f75])).
% 1.23/0.52  fof(f36,plain,(
% 1.23/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.23/0.52    inference(cnf_transformation,[],[f8])).
% 1.23/0.52  fof(f8,axiom,(
% 1.23/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.23/0.52  fof(f73,plain,(
% 1.23/0.52    spl7_4),
% 1.23/0.52    inference(avatar_split_clause,[],[f37,f71])).
% 1.23/0.52  fof(f37,plain,(
% 1.23/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.23/0.52    inference(cnf_transformation,[],[f8])).
% 1.23/0.52  fof(f69,plain,(
% 1.23/0.52    spl7_3),
% 1.23/0.52    inference(avatar_split_clause,[],[f35,f67])).
% 1.23/0.52  fof(f35,plain,(
% 1.23/0.52    v1_xboole_0(k1_xboole_0)),
% 1.23/0.52    inference(cnf_transformation,[],[f2])).
% 1.23/0.52  fof(f2,axiom,(
% 1.23/0.52    v1_xboole_0(k1_xboole_0)),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.23/0.52  fof(f65,plain,(
% 1.23/0.52    ~spl7_1 | spl7_2),
% 1.23/0.52    inference(avatar_split_clause,[],[f33,f63,f60])).
% 1.23/0.52  fof(f33,plain,(
% 1.23/0.52    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  % SZS output end Proof for theBenchmark
% 1.23/0.52  % (20295)------------------------------
% 1.23/0.52  % (20295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (20295)Termination reason: Refutation
% 1.23/0.52  
% 1.23/0.52  % (20295)Memory used [KB]: 10874
% 1.23/0.52  % (20295)Time elapsed: 0.119 s
% 1.23/0.52  % (20295)------------------------------
% 1.23/0.52  % (20295)------------------------------
% 1.23/0.52  % (20278)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.52  % (20276)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.52  
% 1.23/0.52  % (20276)Memory used [KB]: 1791
% 1.23/0.52  % (20276)Time elapsed: 0.112 s
% 1.23/0.52  % (20276)------------------------------
% 1.23/0.52  % (20276)------------------------------
% 1.23/0.52  % (20275)Success in time 0.169 s
%------------------------------------------------------------------------------
