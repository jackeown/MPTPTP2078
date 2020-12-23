%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:08 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 234 expanded)
%              Number of leaves         :   19 (  72 expanded)
%              Depth                    :   15
%              Number of atoms          :  320 (1051 expanded)
%              Number of equality atoms :  144 ( 488 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f106,f116,f118,f123,f125])).

fof(f125,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f65,f84])).

fof(f84,plain,(
    k1_xboole_0 != sK1 ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X1] :
      ( sK1 != X1
      | k1_xboole_0 != X1 ) ),
    inference(superposition,[],[f81,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( o_1_0_funct_1(X0) = k1_funct_1(sK6(X0,X1),X3)
          | ~ r2_hidden(X3,X1) )
      & k1_relat_1(sK6(X0,X1)) = X1
      & v1_funct_1(sK6(X0,X1))
      & v1_relat_1(sK6(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = o_1_0_funct_1(X0)
              | ~ r2_hidden(X3,X1) )
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( o_1_0_funct_1(X0) = k1_funct_1(sK6(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & k1_relat_1(sK6(X0,X1)) = X1
        & v1_funct_1(sK6(X0,X1))
        & v1_relat_1(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = o_1_0_funct_1(X0)
          | ~ r2_hidden(X3,X1) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = o_1_0_funct_1(X0) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK6(X0,X1))
      | k1_xboole_0 != k1_relat_1(sK6(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f79,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK6(X0,X1))
      | ~ v1_relat_1(sK6(X0,X1))
      | k1_xboole_0 != k1_relat_1(sK6(X0,X1)) ) ),
    inference(resolution,[],[f78,f52])).

fof(f52,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k1_relat_1(X0) != sK1
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f77,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f77,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | k1_relat_1(X0) != sK1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f35,f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f35,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).

fof(f17,plain,
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

fof(f11,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f65,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f123,plain,
    ( spl7_1
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl7_1
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f120,f61])).

fof(f61,plain,
    ( k1_xboole_0 != sK0
    | spl7_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f120,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_5 ),
    inference(resolution,[],[f115,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f115,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl7_5
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f118,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl7_4 ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,
    ( ! [X0] : sK1 != X0
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_4
  <=> ! [X0] : sK1 != X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f116,plain,
    ( spl7_5
    | spl7_4
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f112,f101,f104,f114])).

fof(f101,plain,
    ( spl7_3
  <=> ! [X1] : sK4(k1_tarski(X1),sK0) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( sK1 != X0
        | ~ r2_hidden(X1,sK0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f111,f83])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( sK1 != X0
        | ~ r2_hidden(X1,sK0)
        | k1_xboole_0 = X0 )
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( sK1 != X0
        | ~ r2_hidden(X1,sK0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X0 )
    | ~ spl7_3 ),
    inference(superposition,[],[f109,f41])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f20])).

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

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f109,plain,
    ( ! [X0,X1] :
        ( sK1 != k1_relat_1(sK2(X1,X0))
        | ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = X1 )
    | ~ spl7_3 ),
    inference(resolution,[],[f107,f95])).

fof(f95,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_tarski(X5),sK0)
      | sK1 != k1_relat_1(sK2(X4,X5))
      | k1_xboole_0 = X4 ) ),
    inference(subsumption_resolution,[],[f94,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_tarski(X5),sK0)
      | sK1 != k1_relat_1(sK2(X4,X5))
      | ~ v1_relat_1(sK2(X4,X5))
      | k1_xboole_0 = X4 ) ),
    inference(subsumption_resolution,[],[f90,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f90,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_tarski(X5),sK0)
      | sK1 != k1_relat_1(sK2(X4,X5))
      | ~ v1_funct_1(sK2(X4,X5))
      | ~ v1_relat_1(sK2(X4,X5))
      | k1_xboole_0 = X4 ) ),
    inference(superposition,[],[f35,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f107,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tarski(X0),sK0)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl7_3 ),
    inference(superposition,[],[f46,f102])).

fof(f102,plain,
    ( ! [X1] : sK4(k1_tarski(X1),sK0) = X1
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f106,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f99,f104,f101])).

fof(f99,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1 ) ),
    inference(subsumption_resolution,[],[f98,f83])).

fof(f98,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f96,f41])).

fof(f96,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X0))
      | sK4(k1_tarski(X0),sK0) = X0
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f69,f95])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | sK4(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f45,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f34,f63,f59])).

fof(f34,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:06:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.53  % (11746)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (11751)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (11760)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (11744)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (11751)Refutation not found, incomplete strategy% (11751)------------------------------
% 0.21/0.56  % (11751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (11751)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (11751)Memory used [KB]: 10618
% 0.21/0.56  % (11751)Time elapsed: 0.112 s
% 0.21/0.56  % (11751)------------------------------
% 0.21/0.56  % (11751)------------------------------
% 0.21/0.56  % (11770)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (11743)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.57  % (11757)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % (11747)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (11750)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.58  % (11744)Refutation not found, incomplete strategy% (11744)------------------------------
% 0.21/0.58  % (11744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (11744)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (11744)Memory used [KB]: 10618
% 0.21/0.58  % (11744)Time elapsed: 0.142 s
% 0.21/0.58  % (11744)------------------------------
% 0.21/0.58  % (11744)------------------------------
% 0.21/0.58  % (11745)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.59  % (11752)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.59  % (11766)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.59  % (11752)Refutation not found, incomplete strategy% (11752)------------------------------
% 0.21/0.59  % (11752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (11752)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (11752)Memory used [KB]: 10618
% 0.21/0.59  % (11752)Time elapsed: 0.159 s
% 0.21/0.59  % (11752)------------------------------
% 0.21/0.59  % (11752)------------------------------
% 1.76/0.60  % (11742)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.76/0.60  % (11742)Refutation not found, incomplete strategy% (11742)------------------------------
% 1.76/0.60  % (11742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (11742)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.60  
% 1.76/0.60  % (11742)Memory used [KB]: 1663
% 1.76/0.60  % (11742)Time elapsed: 0.159 s
% 1.76/0.60  % (11742)------------------------------
% 1.76/0.60  % (11742)------------------------------
% 1.76/0.60  % (11765)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.76/0.60  % (11750)Refutation not found, incomplete strategy% (11750)------------------------------
% 1.76/0.60  % (11750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (11750)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.60  
% 1.76/0.60  % (11750)Memory used [KB]: 10618
% 1.76/0.60  % (11750)Time elapsed: 0.178 s
% 1.76/0.60  % (11750)------------------------------
% 1.76/0.60  % (11750)------------------------------
% 1.76/0.60  % (11749)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.76/0.61  % (11754)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.76/0.61  % (11768)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.76/0.61  % (11745)Refutation found. Thanks to Tanya!
% 1.76/0.61  % SZS status Theorem for theBenchmark
% 1.76/0.61  % SZS output start Proof for theBenchmark
% 1.76/0.61  fof(f126,plain,(
% 1.76/0.61    $false),
% 1.76/0.61    inference(avatar_sat_refutation,[],[f66,f106,f116,f118,f123,f125])).
% 1.76/0.61  fof(f125,plain,(
% 1.76/0.61    ~spl7_2),
% 1.76/0.61    inference(avatar_contradiction_clause,[],[f124])).
% 1.76/0.61  fof(f124,plain,(
% 1.76/0.61    $false | ~spl7_2),
% 1.76/0.61    inference(subsumption_resolution,[],[f65,f84])).
% 1.76/0.61  fof(f84,plain,(
% 1.76/0.61    k1_xboole_0 != sK1),
% 1.76/0.61    inference(equality_resolution,[],[f83])).
% 1.76/0.61  fof(f83,plain,(
% 1.76/0.61    ( ! [X1] : (sK1 != X1 | k1_xboole_0 != X1) )),
% 1.76/0.61    inference(superposition,[],[f81,f53])).
% 1.76/0.61  fof(f53,plain,(
% 1.76/0.61    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X1) )),
% 1.76/0.61    inference(cnf_transformation,[],[f33])).
% 1.76/0.61  fof(f33,plain,(
% 1.76/0.61    ! [X0,X1] : (! [X3] : (o_1_0_funct_1(X0) = k1_funct_1(sK6(X0,X1),X3) | ~r2_hidden(X3,X1)) & k1_relat_1(sK6(X0,X1)) = X1 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1)))),
% 1.76/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f32])).
% 1.76/0.61  fof(f32,plain,(
% 1.76/0.61    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = o_1_0_funct_1(X0) | ~r2_hidden(X3,X1)) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (o_1_0_funct_1(X0) = k1_funct_1(sK6(X0,X1),X3) | ~r2_hidden(X3,X1)) & k1_relat_1(sK6(X0,X1)) = X1 & v1_funct_1(sK6(X0,X1)) & v1_relat_1(sK6(X0,X1))))),
% 1.76/0.61    introduced(choice_axiom,[])).
% 1.76/0.61  fof(f16,plain,(
% 1.76/0.61    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = o_1_0_funct_1(X0) | ~r2_hidden(X3,X1)) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.76/0.61    inference(ennf_transformation,[],[f6])).
% 1.76/0.61  fof(f6,axiom,(
% 1.76/0.61    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X1) => k1_funct_1(X2,X3) = o_1_0_funct_1(X0)) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).
% 1.76/0.61  fof(f81,plain,(
% 1.76/0.61    ( ! [X0,X1] : (sK1 != k1_relat_1(sK6(X0,X1)) | k1_xboole_0 != k1_relat_1(sK6(X0,X1))) )),
% 1.76/0.61    inference(subsumption_resolution,[],[f79,f51])).
% 1.76/0.61  fof(f51,plain,(
% 1.76/0.61    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f33])).
% 1.76/0.61  fof(f79,plain,(
% 1.76/0.61    ( ! [X0,X1] : (sK1 != k1_relat_1(sK6(X0,X1)) | ~v1_relat_1(sK6(X0,X1)) | k1_xboole_0 != k1_relat_1(sK6(X0,X1))) )),
% 1.76/0.61    inference(resolution,[],[f78,f52])).
% 1.76/0.61  fof(f52,plain,(
% 1.76/0.61    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 1.76/0.61    inference(cnf_transformation,[],[f33])).
% 1.76/0.61  fof(f78,plain,(
% 1.76/0.61    ( ! [X0] : (~v1_funct_1(X0) | k1_relat_1(X0) != sK1 | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 1.76/0.61    inference(subsumption_resolution,[],[f77,f36])).
% 1.76/0.61  fof(f36,plain,(
% 1.76/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f3])).
% 1.76/0.61  fof(f3,axiom,(
% 1.76/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.76/0.61  fof(f77,plain,(
% 1.76/0.61    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 1.76/0.61    inference(duplicate_literal_removal,[],[f76])).
% 1.76/0.61  fof(f76,plain,(
% 1.76/0.61    ( ! [X0] : (~r1_tarski(k1_xboole_0,sK0) | k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.76/0.61    inference(superposition,[],[f35,f37])).
% 1.76/0.61  fof(f37,plain,(
% 1.76/0.61    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f19])).
% 1.76/0.61  fof(f19,plain,(
% 1.76/0.61    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.76/0.61    inference(nnf_transformation,[],[f12])).
% 1.76/0.61  fof(f12,plain,(
% 1.76/0.61    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.76/0.61    inference(ennf_transformation,[],[f5])).
% 1.76/0.61  fof(f5,axiom,(
% 1.76/0.61    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.76/0.61  fof(f35,plain,(
% 1.76/0.61    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f18])).
% 1.76/0.61  fof(f18,plain,(
% 1.76/0.61    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0)),
% 1.76/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).
% 1.76/0.61  fof(f17,plain,(
% 1.76/0.61    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK0))),
% 1.76/0.61    introduced(choice_axiom,[])).
% 1.76/0.61  fof(f11,plain,(
% 1.76/0.61    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.76/0.61    inference(flattening,[],[f10])).
% 1.76/0.61  fof(f10,plain,(
% 1.76/0.61    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.76/0.61    inference(ennf_transformation,[],[f9])).
% 1.76/0.61  fof(f9,negated_conjecture,(
% 1.76/0.61    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.76/0.61    inference(negated_conjecture,[],[f8])).
% 1.76/0.61  fof(f8,conjecture,(
% 1.76/0.61    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 1.76/0.61  fof(f65,plain,(
% 1.76/0.61    k1_xboole_0 = sK1 | ~spl7_2),
% 1.76/0.61    inference(avatar_component_clause,[],[f63])).
% 1.76/0.61  fof(f63,plain,(
% 1.76/0.61    spl7_2 <=> k1_xboole_0 = sK1),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.76/0.61  fof(f123,plain,(
% 1.76/0.61    spl7_1 | ~spl7_5),
% 1.76/0.61    inference(avatar_contradiction_clause,[],[f122])).
% 1.76/0.61  fof(f122,plain,(
% 1.76/0.61    $false | (spl7_1 | ~spl7_5)),
% 1.76/0.61    inference(subsumption_resolution,[],[f120,f61])).
% 1.76/0.61  fof(f61,plain,(
% 1.76/0.61    k1_xboole_0 != sK0 | spl7_1),
% 1.76/0.61    inference(avatar_component_clause,[],[f59])).
% 1.76/0.61  fof(f59,plain,(
% 1.76/0.61    spl7_1 <=> k1_xboole_0 = sK0),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.76/0.61  fof(f120,plain,(
% 1.76/0.61    k1_xboole_0 = sK0 | ~spl7_5),
% 1.76/0.61    inference(resolution,[],[f115,f43])).
% 1.76/0.61  fof(f43,plain,(
% 1.76/0.61    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.76/0.61    inference(cnf_transformation,[],[f23])).
% 1.76/0.61  fof(f23,plain,(
% 1.76/0.61    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.76/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f22])).
% 1.76/0.61  fof(f22,plain,(
% 1.76/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.76/0.61    introduced(choice_axiom,[])).
% 1.76/0.61  fof(f14,plain,(
% 1.76/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.76/0.61    inference(ennf_transformation,[],[f2])).
% 1.76/0.61  fof(f2,axiom,(
% 1.76/0.61    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.76/0.61  fof(f115,plain,(
% 1.76/0.61    ( ! [X1] : (~r2_hidden(X1,sK0)) ) | ~spl7_5),
% 1.76/0.61    inference(avatar_component_clause,[],[f114])).
% 1.76/0.61  fof(f114,plain,(
% 1.76/0.61    spl7_5 <=> ! [X1] : ~r2_hidden(X1,sK0)),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.76/0.61  fof(f118,plain,(
% 1.76/0.61    ~spl7_4),
% 1.76/0.61    inference(avatar_contradiction_clause,[],[f117])).
% 1.76/0.61  fof(f117,plain,(
% 1.76/0.61    $false | ~spl7_4),
% 1.76/0.61    inference(equality_resolution,[],[f105])).
% 1.76/0.61  fof(f105,plain,(
% 1.76/0.61    ( ! [X0] : (sK1 != X0) ) | ~spl7_4),
% 1.76/0.61    inference(avatar_component_clause,[],[f104])).
% 1.76/0.61  fof(f104,plain,(
% 1.76/0.61    spl7_4 <=> ! [X0] : sK1 != X0),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.76/0.61  fof(f116,plain,(
% 1.76/0.61    spl7_5 | spl7_4 | ~spl7_3),
% 1.76/0.61    inference(avatar_split_clause,[],[f112,f101,f104,f114])).
% 1.76/0.61  fof(f101,plain,(
% 1.76/0.61    spl7_3 <=> ! [X1] : sK4(k1_tarski(X1),sK0) = X1),
% 1.76/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.76/0.61  fof(f112,plain,(
% 1.76/0.61    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0)) ) | ~spl7_3),
% 1.76/0.61    inference(subsumption_resolution,[],[f111,f83])).
% 1.76/0.61  fof(f111,plain,(
% 1.76/0.61    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0) ) | ~spl7_3),
% 1.76/0.61    inference(duplicate_literal_removal,[],[f110])).
% 1.76/0.61  fof(f110,plain,(
% 1.76/0.61    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0 | k1_xboole_0 = X0) ) | ~spl7_3),
% 1.76/0.61    inference(superposition,[],[f109,f41])).
% 1.76/0.61  fof(f41,plain,(
% 1.76/0.61    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.76/0.61    inference(cnf_transformation,[],[f21])).
% 1.76/0.61  fof(f21,plain,(
% 1.76/0.61    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | k1_xboole_0 = X0)),
% 1.76/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f20])).
% 1.76/0.61  fof(f20,plain,(
% 1.76/0.61    ! [X1,X0] : (? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 1.76/0.61    introduced(choice_axiom,[])).
% 1.76/0.61  fof(f13,plain,(
% 1.76/0.61    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.76/0.61    inference(ennf_transformation,[],[f7])).
% 1.76/0.61  fof(f7,axiom,(
% 1.76/0.61    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.76/0.61  fof(f109,plain,(
% 1.76/0.61    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | ~r2_hidden(X0,sK0) | k1_xboole_0 = X1) ) | ~spl7_3),
% 1.76/0.61    inference(resolution,[],[f107,f95])).
% 1.76/0.61  fof(f95,plain,(
% 1.76/0.61    ( ! [X4,X5] : (~r1_tarski(k1_tarski(X5),sK0) | sK1 != k1_relat_1(sK2(X4,X5)) | k1_xboole_0 = X4) )),
% 1.76/0.61    inference(subsumption_resolution,[],[f94,f39])).
% 1.76/0.61  fof(f39,plain,(
% 1.76/0.61    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.76/0.61    inference(cnf_transformation,[],[f21])).
% 1.76/0.61  fof(f94,plain,(
% 1.76/0.61    ( ! [X4,X5] : (~r1_tarski(k1_tarski(X5),sK0) | sK1 != k1_relat_1(sK2(X4,X5)) | ~v1_relat_1(sK2(X4,X5)) | k1_xboole_0 = X4) )),
% 1.76/0.61    inference(subsumption_resolution,[],[f90,f40])).
% 1.76/0.61  fof(f40,plain,(
% 1.76/0.61    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.76/0.61    inference(cnf_transformation,[],[f21])).
% 1.76/0.61  fof(f90,plain,(
% 1.76/0.61    ( ! [X4,X5] : (~r1_tarski(k1_tarski(X5),sK0) | sK1 != k1_relat_1(sK2(X4,X5)) | ~v1_funct_1(sK2(X4,X5)) | ~v1_relat_1(sK2(X4,X5)) | k1_xboole_0 = X4) )),
% 1.76/0.61    inference(superposition,[],[f35,f42])).
% 1.76/0.61  fof(f42,plain,(
% 1.76/0.61    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.76/0.61    inference(cnf_transformation,[],[f21])).
% 1.76/0.61  fof(f107,plain,(
% 1.76/0.61    ( ! [X0] : (r1_tarski(k1_tarski(X0),sK0) | ~r2_hidden(X0,sK0)) ) | ~spl7_3),
% 1.76/0.61    inference(superposition,[],[f46,f102])).
% 1.76/0.61  fof(f102,plain,(
% 1.76/0.61    ( ! [X1] : (sK4(k1_tarski(X1),sK0) = X1) ) | ~spl7_3),
% 1.76/0.61    inference(avatar_component_clause,[],[f101])).
% 1.76/0.61  fof(f46,plain,(
% 1.76/0.61    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f27])).
% 1.76/0.61  fof(f27,plain,(
% 1.76/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.76/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 1.76/0.61  fof(f26,plain,(
% 1.76/0.61    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.76/0.61    introduced(choice_axiom,[])).
% 1.76/0.61  fof(f25,plain,(
% 1.76/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.76/0.61    inference(rectify,[],[f24])).
% 1.76/0.61  fof(f24,plain,(
% 1.76/0.61    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.76/0.61    inference(nnf_transformation,[],[f15])).
% 1.76/0.61  fof(f15,plain,(
% 1.76/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.76/0.61    inference(ennf_transformation,[],[f1])).
% 1.76/0.61  fof(f1,axiom,(
% 1.76/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.76/0.61  fof(f106,plain,(
% 1.76/0.61    spl7_3 | spl7_4),
% 1.76/0.61    inference(avatar_split_clause,[],[f99,f104,f101])).
% 1.76/0.61  fof(f99,plain,(
% 1.76/0.61    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1) )),
% 1.76/0.61    inference(subsumption_resolution,[],[f98,f83])).
% 1.76/0.61  fof(f98,plain,(
% 1.76/0.61    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0) )),
% 1.76/0.61    inference(duplicate_literal_removal,[],[f97])).
% 1.76/0.61  fof(f97,plain,(
% 1.76/0.61    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.76/0.61    inference(superposition,[],[f96,f41])).
% 1.76/0.61  fof(f96,plain,(
% 1.76/0.61    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | sK4(k1_tarski(X0),sK0) = X0 | k1_xboole_0 = X1) )),
% 1.76/0.61    inference(resolution,[],[f69,f95])).
% 1.76/0.61  fof(f69,plain,(
% 1.76/0.61    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | sK4(k1_tarski(X0),X1) = X0) )),
% 1.76/0.61    inference(resolution,[],[f45,f57])).
% 1.76/0.61  fof(f57,plain,(
% 1.76/0.61    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.76/0.61    inference(equality_resolution,[],[f47])).
% 1.76/0.61  fof(f47,plain,(
% 1.76/0.61    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.76/0.61    inference(cnf_transformation,[],[f31])).
% 1.76/0.61  fof(f31,plain,(
% 1.76/0.61    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.76/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 1.76/0.61  fof(f30,plain,(
% 1.76/0.61    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.76/0.61    introduced(choice_axiom,[])).
% 1.76/0.61  fof(f29,plain,(
% 1.76/0.61    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.76/0.61    inference(rectify,[],[f28])).
% 1.76/0.61  fof(f28,plain,(
% 1.76/0.61    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.76/0.61    inference(nnf_transformation,[],[f4])).
% 1.76/0.61  fof(f4,axiom,(
% 1.76/0.61    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.76/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.76/0.61  fof(f45,plain,(
% 1.76/0.61    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.76/0.61    inference(cnf_transformation,[],[f27])).
% 1.76/0.61  fof(f66,plain,(
% 1.76/0.61    ~spl7_1 | spl7_2),
% 1.76/0.61    inference(avatar_split_clause,[],[f34,f63,f59])).
% 1.76/0.61  fof(f34,plain,(
% 1.76/0.61    k1_xboole_0 = sK1 | k1_xboole_0 != sK0),
% 1.76/0.61    inference(cnf_transformation,[],[f18])).
% 1.76/0.61  % SZS output end Proof for theBenchmark
% 1.76/0.61  % (11745)------------------------------
% 1.76/0.61  % (11745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.61  % (11745)Termination reason: Refutation
% 1.76/0.61  
% 1.76/0.61  % (11745)Memory used [KB]: 10746
% 1.76/0.61  % (11745)Time elapsed: 0.115 s
% 1.76/0.61  % (11745)------------------------------
% 1.76/0.61  % (11745)------------------------------
% 1.76/0.61  % (11741)Success in time 0.244 s
%------------------------------------------------------------------------------
