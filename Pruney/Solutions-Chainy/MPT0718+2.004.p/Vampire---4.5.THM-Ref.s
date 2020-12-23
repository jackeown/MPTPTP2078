%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 236 expanded)
%              Number of leaves         :   31 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :  423 (1066 expanded)
%              Number of equality atoms :   38 ( 137 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f394,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f106,f137,f140,f142,f144,f180,f182,f188,f265,f274,f374,f389,f393])).

fof(f393,plain,(
    spl4_34 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | spl4_34 ),
    inference(resolution,[],[f388,f44])).

fof(f44,plain,(
    v5_funct_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ v2_relat_1(sK1)
    & k1_relat_1(sK0) = k1_relat_1(sK1)
    & v5_funct_1(sK0,sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_relat_1(X1)
            & k1_relat_1(X0) = k1_relat_1(X1)
            & v5_funct_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X1) = k1_relat_1(sK0)
          & v5_funct_1(sK0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ~ v2_relat_1(X1)
        & k1_relat_1(X1) = k1_relat_1(sK0)
        & v5_funct_1(sK0,X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_relat_1(sK1)
      & k1_relat_1(sK0) = k1_relat_1(sK1)
      & v5_funct_1(sK0,sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_relat_1(X1)
          & k1_relat_1(X0) = k1_relat_1(X1)
          & v5_funct_1(X0,X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k1_relat_1(X0) = k1_relat_1(X1)
                & v5_funct_1(X0,X1) )
             => v2_relat_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k1_relat_1(X1)
              & v5_funct_1(X0,X1) )
           => v2_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_1)).

fof(f388,plain,
    ( ~ v5_funct_1(sK0,sK1)
    | spl4_34 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl4_34
  <=> v5_funct_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f389,plain,
    ( spl4_11
    | ~ spl4_34
    | ~ spl4_10
    | ~ spl4_9
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f384,f372,f122,f126,f386,f130])).

fof(f130,plain,
    ( spl4_11
  <=> v2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f126,plain,
    ( spl4_10
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f122,plain,
    ( spl4_9
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f372,plain,
    ( spl4_31
  <=> ! [X2] :
        ( ~ v1_xboole_0(k1_funct_1(X2,sK2(sK1)))
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v5_funct_1(sK0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f384,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v5_funct_1(sK0,sK1)
    | v2_relat_1(sK1)
    | ~ spl4_31 ),
    inference(duplicate_literal_removal,[],[f383])).

fof(f383,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v5_funct_1(sK0,sK1)
    | v2_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_31 ),
    inference(resolution,[],[f373,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_funct_1(X0,sK2(X0)))
      | v2_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ( v1_xboole_0(k1_funct_1(X0,sK2(X0)))
            & r2_hidden(sK2(X0),k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(k1_funct_1(X0,X1))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( v1_xboole_0(k1_funct_1(X0,sK2(X0)))
        & r2_hidden(sK2(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X2] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X2))
              | ~ r2_hidden(X2,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v2_relat_1(X0)
          | ? [X1] :
              ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1] :
              ( ~ v1_xboole_0(k1_funct_1(X0,X1))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_relat_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_relat_1(X0)
      <=> ! [X1] :
            ( ~ v1_xboole_0(k1_funct_1(X0,X1))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_relat_1(X0)
      <=> ! [X1] :
            ~ ( v1_xboole_0(k1_funct_1(X0,X1))
              & r2_hidden(X1,k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_funct_1)).

fof(f373,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(k1_funct_1(X2,sK2(sK1)))
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v5_funct_1(sK0,X2) )
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f372])).

fof(f374,plain,
    ( ~ spl4_13
    | ~ spl4_14
    | spl4_31
    | ~ spl4_12
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f362,f263,f134,f372,f157,f153])).

fof(f153,plain,
    ( spl4_13
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f157,plain,
    ( spl4_14
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f134,plain,
    ( spl4_12
  <=> r2_hidden(sK2(sK1),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f263,plain,
    ( spl4_25
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f362,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(k1_funct_1(X2,sK2(sK1)))
        | ~ v5_funct_1(sK0,X2)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl4_12
    | ~ spl4_25 ),
    inference(resolution,[],[f289,f136])).

fof(f136,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f289,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_hidden(X8,k1_relat_1(X9))
        | ~ v1_xboole_0(k1_funct_1(X7,X8))
        | ~ v5_funct_1(X9,X7)
        | ~ v1_funct_1(X9)
        | ~ v1_relat_1(X9)
        | ~ v1_funct_1(X7)
        | ~ v1_relat_1(X7) )
    | ~ spl4_25 ),
    inference(resolution,[],[f278,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
      | ~ r2_hidden(X3,k1_relat_1(X1))
      | ~ v5_funct_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1)))
                & r2_hidden(sK3(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1)))
        & r2_hidden(sK3(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(f278,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_25 ),
    inference(superposition,[],[f264,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f264,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f263])).

fof(f274,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | ~ spl4_1 ),
    inference(resolution,[],[f78,f40])).

fof(f40,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_1
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f265,plain,
    ( ~ spl4_2
    | ~ spl4_6
    | spl4_25 ),
    inference(avatar_split_clause,[],[f261,f263,f103,f80])).

fof(f80,plain,
    ( spl4_2
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f103,plain,
    ( spl4_6
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f261,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f255,f47])).

fof(f47,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f255,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(condensation,[],[f254])).

fof(f254,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(trivial_inequality_removal,[],[f251])).

fof(f251,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f210,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

fof(f210,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X0,k5_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2))))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f67,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) = k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0)),k2_enumset1(k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1))),k3_xboole_0(k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0)),k2_enumset1(k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1))))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f65,f66,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) ),
    inference(definition_unfolding,[],[f60,f61,f50,f50])).

fof(f50,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X1,k1_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) )
       => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).

fof(f67,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f59,f61,f50])).

fof(f59,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f188,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl4_5 ),
    inference(resolution,[],[f183,f40])).

fof(f183,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f101,f41])).

fof(f41,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

% (9553)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f101,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_5
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f182,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl4_14 ),
    inference(resolution,[],[f159,f41])).

fof(f159,plain,
    ( ~ v1_funct_1(sK0)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f157])).

fof(f180,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl4_13 ),
    inference(resolution,[],[f155,f40])).

fof(f155,plain,
    ( ~ v1_relat_1(sK0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f153])).

fof(f144,plain,(
    ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl4_11 ),
    inference(resolution,[],[f132,f46])).

fof(f46,plain,(
    ~ v2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f132,plain,
    ( v2_relat_1(sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f142,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | spl4_10 ),
    inference(resolution,[],[f128,f43])).

fof(f43,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f128,plain,
    ( ~ v1_funct_1(sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f140,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl4_9 ),
    inference(resolution,[],[f124,f42])).

fof(f42,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f124,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f137,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | spl4_11
    | spl4_12 ),
    inference(avatar_split_clause,[],[f118,f134,f130,f126,f122])).

fof(f118,plain,
    ( r2_hidden(sK2(sK1),k1_relat_1(sK0))
    | v2_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f54,f45])).

fof(f45,plain,(
    k1_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | v2_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f106,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f98,f103,f100])).

fof(f98,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( v1_funct_1(k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f64,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f83,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f75,f80,f77])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f62,f52])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:41:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.41  % (9551)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.44  % (9542)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (9549)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (9539)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (9541)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (9549)Refutation not found, incomplete strategy% (9549)------------------------------
% 0.21/0.46  % (9549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (9549)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (9549)Memory used [KB]: 10874
% 0.21/0.46  % (9549)Time elapsed: 0.079 s
% 0.21/0.46  % (9549)------------------------------
% 0.21/0.46  % (9549)------------------------------
% 0.21/0.47  % (9540)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (9542)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f394,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f83,f106,f137,f140,f142,f144,f180,f182,f188,f265,f274,f374,f389,f393])).
% 0.21/0.47  fof(f393,plain,(
% 0.21/0.47    spl4_34),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f390])).
% 0.21/0.47  fof(f390,plain,(
% 0.21/0.47    $false | spl4_34),
% 0.21/0.47    inference(resolution,[],[f388,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    v5_funct_1(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    (~v2_relat_1(sK1) & k1_relat_1(sK0) = k1_relat_1(sK1) & v5_funct_1(sK0,sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f30,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(sK0) & v5_funct_1(sK0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ? [X1] : (~v2_relat_1(X1) & k1_relat_1(X1) = k1_relat_1(sK0) & v5_funct_1(sK0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~v2_relat_1(sK1) & k1_relat_1(sK0) = k1_relat_1(sK1) & v5_funct_1(sK0,sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~v2_relat_1(X1) & k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((~v2_relat_1(X1) & (k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1)) => v2_relat_1(X1))))),
% 0.21/0.47    inference(negated_conjecture,[],[f14])).
% 0.21/0.47  fof(f14,conjecture,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k1_relat_1(X1) & v5_funct_1(X0,X1)) => v2_relat_1(X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_funct_1)).
% 0.21/0.47  fof(f388,plain,(
% 0.21/0.47    ~v5_funct_1(sK0,sK1) | spl4_34),
% 0.21/0.47    inference(avatar_component_clause,[],[f386])).
% 0.21/0.47  fof(f386,plain,(
% 0.21/0.47    spl4_34 <=> v5_funct_1(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.47  fof(f389,plain,(
% 0.21/0.47    spl4_11 | ~spl4_34 | ~spl4_10 | ~spl4_9 | ~spl4_31),
% 0.21/0.47    inference(avatar_split_clause,[],[f384,f372,f122,f126,f386,f130])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    spl4_11 <=> v2_relat_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    spl4_10 <=> v1_funct_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    spl4_9 <=> v1_relat_1(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.47  fof(f372,plain,(
% 0.21/0.47    spl4_31 <=> ! [X2] : (~v1_xboole_0(k1_funct_1(X2,sK2(sK1))) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v5_funct_1(sK0,X2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.47  fof(f384,plain,(
% 0.21/0.47    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v5_funct_1(sK0,sK1) | v2_relat_1(sK1) | ~spl4_31),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f383])).
% 0.21/0.47  fof(f383,plain,(
% 0.21/0.47    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v5_funct_1(sK0,sK1) | v2_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_31),
% 0.21/0.47    inference(resolution,[],[f373,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0] : (v1_xboole_0(k1_funct_1(X0,sK2(X0))) | v2_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0] : (((v2_relat_1(X0) | (v1_xboole_0(k1_funct_1(X0,sK2(X0))) & r2_hidden(sK2(X0),k1_relat_1(X0)))) & (! [X2] : (~v1_xboole_0(k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X0))) | ~v2_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0] : (? [X1] : (v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0))) => (v1_xboole_0(k1_funct_1(X0,sK2(X0))) & r2_hidden(sK2(X0),k1_relat_1(X0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0] : (((v2_relat_1(X0) | ? [X1] : (v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X2] : (~v1_xboole_0(k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X0))) | ~v2_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(rectify,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0] : (((v2_relat_1(X0) | ? [X1] : (v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_relat_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : ((v2_relat_1(X0) <=> ! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : ((v2_relat_1(X0) <=> ! [X1] : (~v1_xboole_0(k1_funct_1(X0,X1)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_relat_1(X0) <=> ! [X1] : ~(v1_xboole_0(k1_funct_1(X0,X1)) & r2_hidden(X1,k1_relat_1(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_funct_1)).
% 0.21/0.47  fof(f373,plain,(
% 0.21/0.47    ( ! [X2] : (~v1_xboole_0(k1_funct_1(X2,sK2(sK1))) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v5_funct_1(sK0,X2)) ) | ~spl4_31),
% 0.21/0.47    inference(avatar_component_clause,[],[f372])).
% 0.21/0.47  fof(f374,plain,(
% 0.21/0.47    ~spl4_13 | ~spl4_14 | spl4_31 | ~spl4_12 | ~spl4_25),
% 0.21/0.47    inference(avatar_split_clause,[],[f362,f263,f134,f372,f157,f153])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    spl4_13 <=> v1_relat_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    spl4_14 <=> v1_funct_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    spl4_12 <=> r2_hidden(sK2(sK1),k1_relat_1(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.47  fof(f263,plain,(
% 0.21/0.47    spl4_25 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.47  fof(f362,plain,(
% 0.21/0.47    ( ! [X2] : (~v1_xboole_0(k1_funct_1(X2,sK2(sK1))) | ~v5_funct_1(sK0,X2) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | (~spl4_12 | ~spl4_25)),
% 0.21/0.47    inference(resolution,[],[f289,f136])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    r2_hidden(sK2(sK1),k1_relat_1(sK0)) | ~spl4_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f134])).
% 0.21/0.47  fof(f289,plain,(
% 0.21/0.47    ( ! [X8,X7,X9] : (~r2_hidden(X8,k1_relat_1(X9)) | ~v1_xboole_0(k1_funct_1(X7,X8)) | ~v5_funct_1(X9,X7) | ~v1_funct_1(X9) | ~v1_relat_1(X9) | ~v1_funct_1(X7) | ~v1_relat_1(X7)) ) | ~spl4_25),
% 0.21/0.47    inference(resolution,[],[f278,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1)) | ~v5_funct_1(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1))) & r2_hidden(sK3(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK3(X0,X1)),k1_funct_1(X0,sK3(X0,X1))) & r2_hidden(sK3(X0,X1),k1_relat_1(X1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(rectify,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).
% 0.21/0.47  fof(f278,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) ) | ~spl4_25),
% 0.21/0.47    inference(superposition,[],[f264,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.47  fof(f264,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_25),
% 0.21/0.47    inference(avatar_component_clause,[],[f263])).
% 0.21/0.47  fof(f274,plain,(
% 0.21/0.47    ~spl4_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f271])).
% 0.21/0.47  fof(f271,plain,(
% 0.21/0.47    $false | ~spl4_1),
% 0.21/0.47    inference(resolution,[],[f78,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    v1_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl4_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl4_1 <=> ! [X0] : ~v1_relat_1(X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f265,plain,(
% 0.21/0.47    ~spl4_2 | ~spl4_6 | spl4_25),
% 0.21/0.47    inference(avatar_split_clause,[],[f261,f263,f103,f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl4_2 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl4_6 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.47  fof(f261,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f255,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.47  fof(f255,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.47    inference(condensation,[],[f254])).
% 0.21/0.47  fof(f254,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k1_xboole_0)) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f251])).
% 0.21/0.47  fof(f251,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X1,k1_relat_1(k1_xboole_0)) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.47    inference(superposition,[],[f210,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_xboole_0 != k9_relat_1(X0,k5_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)),k3_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X2,X2,X2,X2)))) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(superposition,[],[f67,f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k9_relat_1(X2,k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) = k5_xboole_0(k5_xboole_0(k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0)),k2_enumset1(k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1))),k3_xboole_0(k2_enumset1(k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0),k1_funct_1(X2,X0)),k2_enumset1(k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1),k1_funct_1(X2,X1)))) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f65,f66,f66])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f60,f61,f50,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | ~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(flattening,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1)) | (~r2_hidden(X1,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X1,k1_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) => k9_relat_1(X2,k2_tarski(X0,X1)) = k2_tarski(k1_funct_1(X2,X0),k1_funct_1(X2,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_funct_1)).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k5_xboole_0(k2_enumset1(X0,X0,X0,X0),X1),k3_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f59,f61,f50])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    ~spl4_5),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f186])).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    $false | ~spl4_5),
% 0.21/0.47    inference(resolution,[],[f183,f40])).
% 0.21/0.47  fof(f183,plain,(
% 0.21/0.47    ~v1_relat_1(sK0) | ~spl4_5),
% 0.21/0.47    inference(resolution,[],[f101,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    v1_funct_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  % (9553)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl4_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f100])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl4_5 <=> ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.47  fof(f182,plain,(
% 0.21/0.47    spl4_14),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f181])).
% 0.21/0.47  fof(f181,plain,(
% 0.21/0.47    $false | spl4_14),
% 0.21/0.47    inference(resolution,[],[f159,f41])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    ~v1_funct_1(sK0) | spl4_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f157])).
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    spl4_13),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    $false | spl4_13),
% 0.21/0.47    inference(resolution,[],[f155,f40])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    ~v1_relat_1(sK0) | spl4_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f153])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    ~spl4_11),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f143])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    $false | ~spl4_11),
% 0.21/0.47    inference(resolution,[],[f132,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ~v2_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    v2_relat_1(sK1) | ~spl4_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f130])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    spl4_10),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f141])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    $false | spl4_10),
% 0.21/0.47    inference(resolution,[],[f128,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    v1_funct_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    ~v1_funct_1(sK1) | spl4_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f126])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    spl4_9),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f138])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    $false | spl4_9),
% 0.21/0.47    inference(resolution,[],[f124,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ~v1_relat_1(sK1) | spl4_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f122])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    ~spl4_9 | ~spl4_10 | spl4_11 | spl4_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f118,f134,f130,f126,f122])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    r2_hidden(sK2(sK1),k1_relat_1(sK0)) | v2_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 0.21/0.47    inference(superposition,[],[f54,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    k1_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK2(X0),k1_relat_1(X0)) | v2_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl4_5 | spl4_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f98,f103,f100])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X0] : (v1_funct_1(k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f97])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ( ! [X0] : (v1_funct_1(k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(superposition,[],[f64,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl4_1 | spl4_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f75,f80,f77])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(superposition,[],[f62,f52])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (9542)------------------------------
% 0.21/0.47  % (9542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (9542)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (9542)Memory used [KB]: 6268
% 0.21/0.47  % (9542)Time elapsed: 0.088 s
% 0.21/0.47  % (9542)------------------------------
% 0.21/0.47  % (9542)------------------------------
% 0.21/0.47  % (9544)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (9537)Success in time 0.117 s
%------------------------------------------------------------------------------
