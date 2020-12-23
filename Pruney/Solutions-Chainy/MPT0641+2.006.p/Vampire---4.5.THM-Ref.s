%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:39 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 780 expanded)
%              Number of leaves         :   25 ( 249 expanded)
%              Depth                    :   28
%              Number of atoms          :  703 (5001 expanded)
%              Number of equality atoms :  109 ( 812 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f829,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f113,f242,f526,f553,f787,f828])).

fof(f828,plain,(
    spl11_6 ),
    inference(avatar_contradiction_clause,[],[f827])).

fof(f827,plain,
    ( $false
    | spl11_6 ),
    inference(subsumption_resolution,[],[f220,f826])).

fof(f826,plain,(
    sP0(k5_relat_1(sK6,sK5)) ),
    inference(subsumption_resolution,[],[f825,f53])).

fof(f53,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( ~ v2_funct_1(sK5)
      | ~ v2_funct_1(sK6) )
    & k1_relat_1(sK5) = k2_relat_1(sK6)
    & v2_funct_1(k5_relat_1(sK6,sK5))
    & v1_funct_1(sK6)
    & v1_relat_1(sK6)
    & v1_funct_1(sK5)
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f12,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v2_funct_1(X0)
              | ~ v2_funct_1(X1) )
            & k1_relat_1(X0) = k2_relat_1(X1)
            & v2_funct_1(k5_relat_1(X1,X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ( ~ v2_funct_1(sK5)
            | ~ v2_funct_1(X1) )
          & k2_relat_1(X1) = k1_relat_1(sK5)
          & v2_funct_1(k5_relat_1(X1,sK5))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK5)
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ( ~ v2_funct_1(sK5)
          | ~ v2_funct_1(X1) )
        & k2_relat_1(X1) = k1_relat_1(sK5)
        & v2_funct_1(k5_relat_1(X1,sK5))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ v2_funct_1(sK5)
        | ~ v2_funct_1(sK6) )
      & k1_relat_1(sK5) = k2_relat_1(sK6)
      & v2_funct_1(k5_relat_1(sK6,sK5))
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_funct_1(X0)
            | ~ v2_funct_1(X1) )
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_funct_1(X0)
            | ~ v2_funct_1(X1) )
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(k5_relat_1(X1,X0)) )
             => ( v2_funct_1(X0)
                & v2_funct_1(X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f825,plain,
    ( ~ v1_relat_1(sK5)
    | sP0(k5_relat_1(sK6,sK5)) ),
    inference(subsumption_resolution,[],[f824,f54])).

fof(f54,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f824,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | sP0(k5_relat_1(sK6,sK5)) ),
    inference(subsumption_resolution,[],[f823,f55])).

fof(f55,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f823,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | sP0(k5_relat_1(sK6,sK5)) ),
    inference(subsumption_resolution,[],[f232,f56])).

fof(f56,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f232,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | sP0(k5_relat_1(sK6,sK5)) ),
    inference(resolution,[],[f170,f57])).

fof(f57,plain,(
    v2_funct_1(k5_relat_1(sK6,sK5)) ),
    inference(cnf_transformation,[],[f36])).

fof(f170,plain,(
    ! [X2,X3] :
      ( ~ v2_funct_1(k5_relat_1(X3,X2))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | sP0(k5_relat_1(X3,X2)) ) ),
    inference(resolution,[],[f168,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_funct_1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f168,plain,(
    ! [X2,X3] :
      ( sP1(k5_relat_1(X3,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f166,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f166,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | sP1(k5_relat_1(X3,X2))
      | ~ v1_relat_1(k5_relat_1(X3,X2)) ) ),
    inference(resolution,[],[f81,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f16,f28,f27])).

fof(f27,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f220,plain,
    ( ~ sP0(k5_relat_1(sK6,sK5))
    | spl11_6 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl11_6
  <=> sP0(k5_relat_1(sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f787,plain,
    ( spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(avatar_contradiction_clause,[],[f786])).

fof(f786,plain,
    ( $false
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f785,f112])).

fof(f112,plain,
    ( ~ sP0(sK5)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl11_3
  <=> sP0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f785,plain,
    ( sP0(sK5)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(trivial_inequality_removal,[],[f783])).

fof(f783,plain,
    ( sK7(sK5) != sK7(sK5)
    | sP0(sK5)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(superposition,[],[f67,f766])).

fof(f766,plain,
    ( sK7(sK5) = sK8(sK5)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(forward_demodulation,[],[f757,f138])).

fof(f138,plain,
    ( sK7(sK5) = k1_funct_1(sK6,sK10(sK7(sK5),sK6))
    | spl11_3 ),
    inference(resolution,[],[f77,f132])).

fof(f132,plain,
    ( sP2(sK7(sK5),sK6)
    | spl11_3 ),
    inference(subsumption_resolution,[],[f129,f118])).

fof(f118,plain,(
    sP4(sK6) ),
    inference(subsumption_resolution,[],[f116,f55])).

fof(f116,plain,
    ( sP4(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f79,f56])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP4(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( sP4(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f20,f32,f31,f30])).

fof(f30,plain,(
    ! [X2,X0] :
      ( sP2(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f31,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP2(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP3(X0,X1) )
      | ~ sP4(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f129,plain,
    ( sP2(sK7(sK5),sK6)
    | ~ sP4(sK6)
    | spl11_3 ),
    inference(resolution,[],[f125,f120])).

fof(f120,plain,
    ( r2_hidden(sK7(sK5),k2_relat_1(sK6))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f119,f112])).

fof(f119,plain,
    ( r2_hidden(sK7(sK5),k2_relat_1(sK6))
    | sP0(sK5) ),
    inference(superposition,[],[f64,f58])).

fof(f58,plain,(
    k1_relat_1(sK5) = k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( sK7(X0) != sK8(X0)
          & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0))
          & r2_hidden(sK8(X0),k1_relat_1(X0))
          & r2_hidden(sK7(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK7(X0) != sK8(X0)
        & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0))
        & r2_hidden(sK8(X0),k1_relat_1(X0))
        & r2_hidden(sK7(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1,X2] :
            ( X1 != X2
            & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            & r2_hidden(X2,k1_relat_1(X0))
            & r2_hidden(X1,k1_relat_1(X0)) ) )
      & ( ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(X1))
      | sP2(X0,X1)
      | ~ sP4(X1) ) ),
    inference(resolution,[],[f72,f87])).

fof(f87,plain,(
    ! [X0] :
      ( sP3(X0,k2_relat_1(X0))
      | ~ sP4(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP4(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP3(X0,X1) )
          & ( sP3(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP4(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X0,X1)
      | ~ r2_hidden(X3,X1)
      | sP2(X3,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( ( ~ sP2(sK9(X0,X1),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sP2(sK9(X0,X1),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP2(X3,X0) )
            & ( sP2(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP2(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP2(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP2(sK9(X0,X1),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sP2(sK9(X0,X1),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( ( ~ sP2(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP2(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP2(X3,X0) )
            & ( sP2(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( ( ~ sP2(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP2(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP2(X2,X0) )
            & ( sP2(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP3(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | k1_funct_1(X1,sK10(X0,X1)) = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK10(X0,X1)) = X0
          & r2_hidden(sK10(X0,X1),k1_relat_1(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK10(X0,X1)) = X0
        & r2_hidden(sK10(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ( sP2(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP2(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f757,plain,
    ( sK8(sK5) = k1_funct_1(sK6,sK10(sK7(sK5),sK6))
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(backward_demodulation,[],[f139,f756])).

fof(f756,plain,
    ( sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f754,f544])).

fof(f544,plain,
    ( r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f543])).

fof(f543,plain,
    ( spl11_21
  <=> r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f754,plain,
    ( ~ r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))
    | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(trivial_inequality_removal,[],[f753])).

fof(f753,plain,
    ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(sK5,sK7(sK5))
    | ~ r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))
    | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(superposition,[],[f600,f624])).

fof(f624,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6))
    | spl11_3
    | ~ spl11_21 ),
    inference(forward_demodulation,[],[f623,f144])).

fof(f144,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(sK5,sK8(sK5))
    | spl11_3 ),
    inference(resolution,[],[f66,f112])).

fof(f66,plain,(
    ! [X0] :
      ( sP0(X0)
      | k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f623,plain,
    ( k1_funct_1(sK5,sK8(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6))
    | spl11_3
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f620,f53])).

fof(f620,plain,
    ( k1_funct_1(sK5,sK8(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6))
    | ~ v1_relat_1(sK5)
    | spl11_3
    | ~ spl11_21 ),
    inference(resolution,[],[f585,f54])).

fof(f585,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(k5_relat_1(sK6,X0),sK10(sK8(sK5),sK6)) = k1_funct_1(X0,sK8(sK5))
        | ~ v1_relat_1(X0) )
    | spl11_3
    | ~ spl11_21 ),
    inference(forward_demodulation,[],[f584,f139])).

fof(f584,plain,
    ( ! [X0] :
        ( k1_funct_1(k5_relat_1(sK6,X0),sK10(sK8(sK5),sK6)) = k1_funct_1(X0,k1_funct_1(sK6,sK10(sK8(sK5),sK6)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f583,f55])).

fof(f583,plain,
    ( ! [X0] :
        ( k1_funct_1(k5_relat_1(sK6,X0),sK10(sK8(sK5),sK6)) = k1_funct_1(X0,k1_funct_1(sK6,sK10(sK8(sK5),sK6)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK6) )
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f579,f56])).

fof(f579,plain,
    ( ! [X0] :
        ( k1_funct_1(k5_relat_1(sK6,X0),sK10(sK8(sK5),sK6)) = k1_funct_1(X0,k1_funct_1(sK6,sK10(sK8(sK5),sK6)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl11_21 ),
    inference(resolution,[],[f544,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f600,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | ~ r2_hidden(X0,k1_relat_1(sK6))
        | sK10(sK7(sK5),sK6) = X0 )
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(forward_demodulation,[],[f599,f212])).

fof(f212,plain,(
    k1_relat_1(sK6) = k1_relat_1(k5_relat_1(sK6,sK5)) ),
    inference(subsumption_resolution,[],[f211,f55])).

fof(f211,plain,
    ( k1_relat_1(sK6) = k1_relat_1(k5_relat_1(sK6,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f210,f89])).

fof(f89,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f210,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK5))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f209,f53])).

fof(f209,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK5))
      | ~ v1_relat_1(sK5)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f60,f58])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f599,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK7(sK5),sK6) = X0
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) )
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f598,f518])).

fof(f518,plain,
    ( r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f517])).

fof(f517,plain,
    ( spl11_18
  <=> r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f598,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))
        | k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK7(sK5),sK6) = X0
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) )
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(forward_demodulation,[],[f597,f212])).

fof(f597,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK7(sK5),sK6) = X0
        | ~ r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5)))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) )
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f594,f221])).

fof(f221,plain,
    ( sP0(k5_relat_1(sK6,sK5))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f219])).

fof(f594,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK7(sK5),sK6) = X0
        | ~ r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5)))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))
        | ~ sP0(k5_relat_1(sK6,sK5)) )
    | spl11_3
    | ~ spl11_18 ),
    inference(superposition,[],[f63,f590])).

fof(f590,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6))
    | spl11_3
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f587,f53])).

fof(f587,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6))
    | ~ v1_relat_1(sK5)
    | spl11_3
    | ~ spl11_18 ),
    inference(resolution,[],[f570,f54])).

fof(f570,plain,
    ( ! [X19] :
        ( ~ v1_funct_1(X19)
        | k1_funct_1(k5_relat_1(sK6,X19),sK10(sK7(sK5),sK6)) = k1_funct_1(X19,sK7(sK5))
        | ~ v1_relat_1(X19) )
    | spl11_3
    | ~ spl11_18 ),
    inference(forward_demodulation,[],[f569,f138])).

fof(f569,plain,
    ( ! [X19] :
        ( k1_funct_1(k5_relat_1(sK6,X19),sK10(sK7(sK5),sK6)) = k1_funct_1(X19,k1_funct_1(sK6,sK10(sK7(sK5),sK6)))
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(X19) )
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f568,f55])).

fof(f568,plain,
    ( ! [X19] :
        ( k1_funct_1(k5_relat_1(sK6,X19),sK10(sK7(sK5),sK6)) = k1_funct_1(X19,k1_funct_1(sK6,sK10(sK7(sK5),sK6)))
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_relat_1(sK6) )
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f562,f56])).

fof(f562,plain,
    ( ! [X19] :
        ( k1_funct_1(k5_relat_1(sK6,X19),sK10(sK7(sK5),sK6)) = k1_funct_1(X19,k1_funct_1(sK6,sK10(sK7(sK5),sK6)))
        | ~ v1_funct_1(X19)
        | ~ v1_relat_1(X19)
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl11_18 ),
    inference(resolution,[],[f82,f518])).

fof(f63,plain,(
    ! [X4,X0,X3] :
      ( k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | X3 = X4
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f139,plain,
    ( sK8(sK5) = k1_funct_1(sK6,sK10(sK8(sK5),sK6))
    | spl11_3 ),
    inference(resolution,[],[f77,f133])).

fof(f133,plain,
    ( sP2(sK8(sK5),sK6)
    | spl11_3 ),
    inference(subsumption_resolution,[],[f130,f118])).

fof(f130,plain,
    ( sP2(sK8(sK5),sK6)
    | ~ sP4(sK6)
    | spl11_3 ),
    inference(resolution,[],[f125,f122])).

fof(f122,plain,
    ( r2_hidden(sK8(sK5),k2_relat_1(sK6))
    | spl11_3 ),
    inference(subsumption_resolution,[],[f121,f112])).

fof(f121,plain,
    ( r2_hidden(sK8(sK5),k2_relat_1(sK6))
    | sP0(sK5) ),
    inference(superposition,[],[f65,f58])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),k1_relat_1(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    ! [X0] :
      ( sK7(X0) != sK8(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f553,plain,
    ( spl11_3
    | spl11_21 ),
    inference(avatar_contradiction_clause,[],[f552])).

fof(f552,plain,
    ( $false
    | spl11_3
    | spl11_21 ),
    inference(subsumption_resolution,[],[f551,f133])).

fof(f551,plain,
    ( ~ sP2(sK8(sK5),sK6)
    | spl11_21 ),
    inference(resolution,[],[f545,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),k1_relat_1(X1))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f545,plain,
    ( ~ r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))
    | spl11_21 ),
    inference(avatar_component_clause,[],[f543])).

fof(f526,plain,
    ( spl11_3
    | spl11_18 ),
    inference(avatar_contradiction_clause,[],[f525])).

fof(f525,plain,
    ( $false
    | spl11_3
    | spl11_18 ),
    inference(subsumption_resolution,[],[f524,f132])).

fof(f524,plain,
    ( ~ sP2(sK7(sK5),sK6)
    | spl11_18 ),
    inference(resolution,[],[f519,f76])).

fof(f519,plain,
    ( ~ r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))
    | spl11_18 ),
    inference(avatar_component_clause,[],[f517])).

fof(f242,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl11_1 ),
    inference(subsumption_resolution,[],[f240,f55])).

fof(f240,plain,
    ( ~ v1_relat_1(sK6)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f239,f56])).

fof(f239,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f238,f57])).

fof(f238,plain,
    ( ~ v2_funct_1(k5_relat_1(sK6,sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | spl11_1 ),
    inference(subsumption_resolution,[],[f237,f94])).

fof(f94,plain,
    ( ~ v2_funct_1(sK6)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl11_1
  <=> v2_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f237,plain,
    ( v2_funct_1(sK6)
    | ~ v2_funct_1(k5_relat_1(sK6,sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(resolution,[],[f236,f89])).

fof(f236,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X0,sK5))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f235,f53])).

fof(f235,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X0,sK5))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f233,f54])).

fof(f233,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k2_relat_1(sK6))
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X0,sK5))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(superposition,[],[f69,f58])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | v2_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

fof(f113,plain,
    ( spl11_2
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f104,f110,f96])).

fof(f96,plain,
    ( spl11_2
  <=> v2_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f104,plain,
    ( ~ sP0(sK5)
    | v2_funct_1(sK5) ),
    inference(resolution,[],[f102,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f102,plain,(
    sP1(sK5) ),
    inference(subsumption_resolution,[],[f100,f53])).

fof(f100,plain,
    ( sP1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f68,f54])).

fof(f99,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f59,f96,f92])).

fof(f59,plain,
    ( ~ v2_funct_1(sK5)
    | ~ v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:29 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.20/0.47  % (27456)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.47  % (27448)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (27447)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (27464)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (27444)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (27446)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (27463)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (27455)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (27454)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (27459)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (27451)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (27453)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (27458)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (27445)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (27457)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (27450)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (27462)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.53  % (27465)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (27467)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.53  % (27469)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.54  % (27449)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.54  % (27466)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.54  % (27461)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.54  % (27460)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.59/0.56  % (27452)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.59/0.57  % (27468)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.69/0.61  % (27469)Refutation found. Thanks to Tanya!
% 1.69/0.61  % SZS status Theorem for theBenchmark
% 1.69/0.61  % SZS output start Proof for theBenchmark
% 1.69/0.61  fof(f829,plain,(
% 1.69/0.61    $false),
% 1.69/0.61    inference(avatar_sat_refutation,[],[f99,f113,f242,f526,f553,f787,f828])).
% 1.69/0.61  fof(f828,plain,(
% 1.69/0.61    spl11_6),
% 1.69/0.61    inference(avatar_contradiction_clause,[],[f827])).
% 1.69/0.61  fof(f827,plain,(
% 1.69/0.61    $false | spl11_6),
% 1.69/0.61    inference(subsumption_resolution,[],[f220,f826])).
% 1.69/0.61  fof(f826,plain,(
% 1.69/0.61    sP0(k5_relat_1(sK6,sK5))),
% 1.69/0.61    inference(subsumption_resolution,[],[f825,f53])).
% 1.69/0.61  fof(f53,plain,(
% 1.69/0.61    v1_relat_1(sK5)),
% 1.69/0.61    inference(cnf_transformation,[],[f36])).
% 1.69/0.61  fof(f36,plain,(
% 1.69/0.61    ((~v2_funct_1(sK5) | ~v2_funct_1(sK6)) & k1_relat_1(sK5) = k2_relat_1(sK6) & v2_funct_1(k5_relat_1(sK6,sK5)) & v1_funct_1(sK6) & v1_relat_1(sK6)) & v1_funct_1(sK5) & v1_relat_1(sK5)),
% 1.69/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f12,f35,f34])).
% 1.69/0.61  fof(f34,plain,(
% 1.69/0.61    ? [X0] : (? [X1] : ((~v2_funct_1(X0) | ~v2_funct_1(X1)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : ((~v2_funct_1(sK5) | ~v2_funct_1(X1)) & k2_relat_1(X1) = k1_relat_1(sK5) & v2_funct_1(k5_relat_1(X1,sK5)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f35,plain,(
% 1.69/0.61    ? [X1] : ((~v2_funct_1(sK5) | ~v2_funct_1(X1)) & k2_relat_1(X1) = k1_relat_1(sK5) & v2_funct_1(k5_relat_1(X1,sK5)) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~v2_funct_1(sK5) | ~v2_funct_1(sK6)) & k1_relat_1(sK5) = k2_relat_1(sK6) & v2_funct_1(k5_relat_1(sK6,sK5)) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f12,plain,(
% 1.69/0.61    ? [X0] : (? [X1] : ((~v2_funct_1(X0) | ~v2_funct_1(X1)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.69/0.61    inference(flattening,[],[f11])).
% 1.69/0.61  fof(f11,plain,(
% 1.69/0.61    ? [X0] : (? [X1] : (((~v2_funct_1(X0) | ~v2_funct_1(X1)) & (k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.69/0.61    inference(ennf_transformation,[],[f10])).
% 1.69/0.61  fof(f10,negated_conjecture,(
% 1.69/0.61    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.69/0.61    inference(negated_conjecture,[],[f9])).
% 1.69/0.61  fof(f9,conjecture,(
% 1.69/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 1.69/0.61  fof(f825,plain,(
% 1.69/0.61    ~v1_relat_1(sK5) | sP0(k5_relat_1(sK6,sK5))),
% 1.69/0.61    inference(subsumption_resolution,[],[f824,f54])).
% 1.69/0.61  fof(f54,plain,(
% 1.69/0.61    v1_funct_1(sK5)),
% 1.69/0.61    inference(cnf_transformation,[],[f36])).
% 1.69/0.61  fof(f824,plain,(
% 1.69/0.61    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | sP0(k5_relat_1(sK6,sK5))),
% 1.69/0.61    inference(subsumption_resolution,[],[f823,f55])).
% 1.69/0.61  fof(f55,plain,(
% 1.69/0.61    v1_relat_1(sK6)),
% 1.69/0.61    inference(cnf_transformation,[],[f36])).
% 1.69/0.61  fof(f823,plain,(
% 1.69/0.61    ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | sP0(k5_relat_1(sK6,sK5))),
% 1.69/0.61    inference(subsumption_resolution,[],[f232,f56])).
% 1.69/0.61  fof(f56,plain,(
% 1.69/0.61    v1_funct_1(sK6)),
% 1.69/0.61    inference(cnf_transformation,[],[f36])).
% 1.69/0.61  fof(f232,plain,(
% 1.69/0.61    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | sP0(k5_relat_1(sK6,sK5))),
% 1.69/0.61    inference(resolution,[],[f170,f57])).
% 1.69/0.61  fof(f57,plain,(
% 1.69/0.61    v2_funct_1(k5_relat_1(sK6,sK5))),
% 1.69/0.61    inference(cnf_transformation,[],[f36])).
% 1.69/0.61  fof(f170,plain,(
% 1.69/0.61    ( ! [X2,X3] : (~v2_funct_1(k5_relat_1(X3,X2)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | sP0(k5_relat_1(X3,X2))) )),
% 1.69/0.61    inference(resolution,[],[f168,f61])).
% 1.69/0.61  fof(f61,plain,(
% 1.69/0.61    ( ! [X0] : (~sP1(X0) | ~v2_funct_1(X0) | sP0(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f37])).
% 1.69/0.61  fof(f37,plain,(
% 1.69/0.61    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 1.69/0.61    inference(nnf_transformation,[],[f28])).
% 1.69/0.61  fof(f28,plain,(
% 1.69/0.61    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 1.69/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.69/0.61  fof(f168,plain,(
% 1.69/0.61    ( ! [X2,X3] : (sP1(k5_relat_1(X3,X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2)) )),
% 1.69/0.61    inference(subsumption_resolution,[],[f166,f83])).
% 1.69/0.61  fof(f83,plain,(
% 1.69/0.61    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f26])).
% 1.69/0.61  fof(f26,plain,(
% 1.69/0.61    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.69/0.61    inference(flattening,[],[f25])).
% 1.69/0.61  fof(f25,plain,(
% 1.69/0.61    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.69/0.61    inference(ennf_transformation,[],[f2])).
% 1.69/0.61  fof(f2,axiom,(
% 1.69/0.61    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.69/0.61  fof(f166,plain,(
% 1.69/0.61    ( ! [X2,X3] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | sP1(k5_relat_1(X3,X2)) | ~v1_relat_1(k5_relat_1(X3,X2))) )),
% 1.69/0.61    inference(resolution,[],[f81,f68])).
% 1.69/0.61  fof(f68,plain,(
% 1.69/0.61    ( ! [X0] : (~v1_funct_1(X0) | sP1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f29])).
% 1.69/0.61  fof(f29,plain,(
% 1.69/0.61    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.61    inference(definition_folding,[],[f16,f28,f27])).
% 1.69/0.61  fof(f27,plain,(
% 1.69/0.61    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 1.69/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.69/0.61  fof(f16,plain,(
% 1.69/0.61    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.61    inference(flattening,[],[f15])).
% 1.69/0.61  fof(f15,plain,(
% 1.69/0.61    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.61    inference(ennf_transformation,[],[f5])).
% 1.69/0.61  fof(f5,axiom,(
% 1.69/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 1.69/0.61  fof(f81,plain,(
% 1.69/0.61    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f22])).
% 1.69/0.61  fof(f22,plain,(
% 1.69/0.61    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.61    inference(flattening,[],[f21])).
% 1.69/0.61  fof(f21,plain,(
% 1.69/0.61    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.61    inference(ennf_transformation,[],[f6])).
% 1.69/0.61  fof(f6,axiom,(
% 1.69/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).
% 1.69/0.61  fof(f220,plain,(
% 1.69/0.61    ~sP0(k5_relat_1(sK6,sK5)) | spl11_6),
% 1.69/0.61    inference(avatar_component_clause,[],[f219])).
% 1.69/0.61  fof(f219,plain,(
% 1.69/0.61    spl11_6 <=> sP0(k5_relat_1(sK6,sK5))),
% 1.69/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 1.69/0.61  fof(f787,plain,(
% 1.69/0.61    spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21),
% 1.69/0.61    inference(avatar_contradiction_clause,[],[f786])).
% 1.69/0.61  fof(f786,plain,(
% 1.69/0.61    $false | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 1.69/0.61    inference(subsumption_resolution,[],[f785,f112])).
% 1.69/0.61  fof(f112,plain,(
% 1.69/0.61    ~sP0(sK5) | spl11_3),
% 1.69/0.61    inference(avatar_component_clause,[],[f110])).
% 1.69/0.61  fof(f110,plain,(
% 1.69/0.61    spl11_3 <=> sP0(sK5)),
% 1.69/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.69/0.61  fof(f785,plain,(
% 1.69/0.61    sP0(sK5) | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 1.69/0.61    inference(trivial_inequality_removal,[],[f783])).
% 1.69/0.61  fof(f783,plain,(
% 1.69/0.61    sK7(sK5) != sK7(sK5) | sP0(sK5) | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 1.69/0.61    inference(superposition,[],[f67,f766])).
% 1.69/0.61  fof(f766,plain,(
% 1.69/0.61    sK7(sK5) = sK8(sK5) | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 1.69/0.61    inference(forward_demodulation,[],[f757,f138])).
% 1.69/0.61  fof(f138,plain,(
% 1.69/0.61    sK7(sK5) = k1_funct_1(sK6,sK10(sK7(sK5),sK6)) | spl11_3),
% 1.69/0.61    inference(resolution,[],[f77,f132])).
% 1.69/0.61  fof(f132,plain,(
% 1.69/0.61    sP2(sK7(sK5),sK6) | spl11_3),
% 1.69/0.61    inference(subsumption_resolution,[],[f129,f118])).
% 1.69/0.61  fof(f118,plain,(
% 1.69/0.61    sP4(sK6)),
% 1.69/0.61    inference(subsumption_resolution,[],[f116,f55])).
% 1.69/0.61  fof(f116,plain,(
% 1.69/0.61    sP4(sK6) | ~v1_relat_1(sK6)),
% 1.69/0.61    inference(resolution,[],[f79,f56])).
% 1.69/0.61  fof(f79,plain,(
% 1.69/0.61    ( ! [X0] : (~v1_funct_1(X0) | sP4(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f33])).
% 1.69/0.61  fof(f33,plain,(
% 1.69/0.61    ! [X0] : (sP4(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.61    inference(definition_folding,[],[f20,f32,f31,f30])).
% 1.69/0.61  fof(f30,plain,(
% 1.69/0.61    ! [X2,X0] : (sP2(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 1.69/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.69/0.61  fof(f31,plain,(
% 1.69/0.61    ! [X0,X1] : (sP3(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP2(X2,X0)))),
% 1.69/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.69/0.61  fof(f32,plain,(
% 1.69/0.61    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP3(X0,X1)) | ~sP4(X0))),
% 1.69/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.69/0.61  fof(f20,plain,(
% 1.69/0.61    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.61    inference(flattening,[],[f19])).
% 1.69/0.61  fof(f19,plain,(
% 1.69/0.61    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.61    inference(ennf_transformation,[],[f4])).
% 1.69/0.61  fof(f4,axiom,(
% 1.69/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.69/0.61  fof(f129,plain,(
% 1.69/0.61    sP2(sK7(sK5),sK6) | ~sP4(sK6) | spl11_3),
% 1.69/0.61    inference(resolution,[],[f125,f120])).
% 1.69/0.61  fof(f120,plain,(
% 1.69/0.61    r2_hidden(sK7(sK5),k2_relat_1(sK6)) | spl11_3),
% 1.69/0.61    inference(subsumption_resolution,[],[f119,f112])).
% 1.69/0.61  fof(f119,plain,(
% 1.69/0.61    r2_hidden(sK7(sK5),k2_relat_1(sK6)) | sP0(sK5)),
% 1.69/0.61    inference(superposition,[],[f64,f58])).
% 1.69/0.61  fof(f58,plain,(
% 1.69/0.61    k1_relat_1(sK5) = k2_relat_1(sK6)),
% 1.69/0.61    inference(cnf_transformation,[],[f36])).
% 1.69/0.61  fof(f64,plain,(
% 1.69/0.61    ( ! [X0] : (r2_hidden(sK7(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f41])).
% 1.69/0.61  fof(f41,plain,(
% 1.69/0.61    ! [X0] : ((sP0(X0) | (sK7(X0) != sK8(X0) & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) & r2_hidden(sK8(X0),k1_relat_1(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 1.69/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f39,f40])).
% 1.69/0.61  fof(f40,plain,(
% 1.69/0.61    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK7(X0) != sK8(X0) & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) & r2_hidden(sK8(X0),k1_relat_1(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0))))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f39,plain,(
% 1.69/0.61    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 1.69/0.61    inference(rectify,[],[f38])).
% 1.69/0.61  fof(f38,plain,(
% 1.69/0.61    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 1.69/0.61    inference(nnf_transformation,[],[f27])).
% 1.69/0.61  fof(f125,plain,(
% 1.69/0.61    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | sP2(X0,X1) | ~sP4(X1)) )),
% 1.69/0.61    inference(resolution,[],[f72,f87])).
% 1.69/0.61  fof(f87,plain,(
% 1.69/0.61    ( ! [X0] : (sP3(X0,k2_relat_1(X0)) | ~sP4(X0)) )),
% 1.69/0.61    inference(equality_resolution,[],[f70])).
% 1.69/0.61  fof(f70,plain,(
% 1.69/0.61    ( ! [X0,X1] : (sP3(X0,X1) | k2_relat_1(X0) != X1 | ~sP4(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f42])).
% 1.69/0.61  fof(f42,plain,(
% 1.69/0.61    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP3(X0,X1)) & (sP3(X0,X1) | k2_relat_1(X0) != X1)) | ~sP4(X0))),
% 1.69/0.61    inference(nnf_transformation,[],[f32])).
% 1.69/0.61  fof(f72,plain,(
% 1.69/0.61    ( ! [X0,X3,X1] : (~sP3(X0,X1) | ~r2_hidden(X3,X1) | sP2(X3,X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f46])).
% 1.69/0.61  fof(f46,plain,(
% 1.69/0.61    ! [X0,X1] : ((sP3(X0,X1) | ((~sP2(sK9(X0,X1),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (sP2(sK9(X0,X1),X0) | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP2(X3,X0)) & (sP2(X3,X0) | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 1.69/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).
% 1.69/0.61  fof(f45,plain,(
% 1.69/0.61    ! [X1,X0] : (? [X2] : ((~sP2(X2,X0) | ~r2_hidden(X2,X1)) & (sP2(X2,X0) | r2_hidden(X2,X1))) => ((~sP2(sK9(X0,X1),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (sP2(sK9(X0,X1),X0) | r2_hidden(sK9(X0,X1),X1))))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f44,plain,(
% 1.69/0.61    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((~sP2(X2,X0) | ~r2_hidden(X2,X1)) & (sP2(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP2(X3,X0)) & (sP2(X3,X0) | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 1.69/0.61    inference(rectify,[],[f43])).
% 1.69/0.61  fof(f43,plain,(
% 1.69/0.61    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((~sP2(X2,X0) | ~r2_hidden(X2,X1)) & (sP2(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP2(X2,X0)) & (sP2(X2,X0) | ~r2_hidden(X2,X1))) | ~sP3(X0,X1)))),
% 1.69/0.61    inference(nnf_transformation,[],[f31])).
% 1.69/0.61  fof(f77,plain,(
% 1.69/0.61    ( ! [X0,X1] : (~sP2(X0,X1) | k1_funct_1(X1,sK10(X0,X1)) = X0) )),
% 1.69/0.61    inference(cnf_transformation,[],[f50])).
% 1.69/0.61  fof(f50,plain,(
% 1.69/0.61    ! [X0,X1] : ((sP2(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK10(X0,X1)) = X0 & r2_hidden(sK10(X0,X1),k1_relat_1(X1))) | ~sP2(X0,X1)))),
% 1.69/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f48,f49])).
% 1.69/0.61  fof(f49,plain,(
% 1.69/0.61    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK10(X0,X1)) = X0 & r2_hidden(sK10(X0,X1),k1_relat_1(X1))))),
% 1.69/0.61    introduced(choice_axiom,[])).
% 1.69/0.61  fof(f48,plain,(
% 1.69/0.61    ! [X0,X1] : ((sP2(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP2(X0,X1)))),
% 1.69/0.61    inference(rectify,[],[f47])).
% 1.69/0.61  fof(f47,plain,(
% 1.69/0.61    ! [X2,X0] : ((sP2(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP2(X2,X0)))),
% 1.69/0.61    inference(nnf_transformation,[],[f30])).
% 1.69/0.61  fof(f757,plain,(
% 1.69/0.61    sK8(sK5) = k1_funct_1(sK6,sK10(sK7(sK5),sK6)) | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 1.69/0.61    inference(backward_demodulation,[],[f139,f756])).
% 1.69/0.61  fof(f756,plain,(
% 1.69/0.61    sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6) | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 1.69/0.61    inference(subsumption_resolution,[],[f754,f544])).
% 1.69/0.61  fof(f544,plain,(
% 1.69/0.61    r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) | ~spl11_21),
% 1.69/0.61    inference(avatar_component_clause,[],[f543])).
% 1.69/0.61  fof(f543,plain,(
% 1.69/0.61    spl11_21 <=> r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))),
% 1.69/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 1.69/0.61  fof(f754,plain,(
% 1.69/0.61    ~r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6) | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 1.69/0.61    inference(trivial_inequality_removal,[],[f753])).
% 1.69/0.61  fof(f753,plain,(
% 1.69/0.61    k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(sK5,sK7(sK5)) | ~r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6) | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 1.69/0.61    inference(superposition,[],[f600,f624])).
% 1.69/0.61  fof(f624,plain,(
% 1.69/0.61    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6)) | (spl11_3 | ~spl11_21)),
% 1.69/0.61    inference(forward_demodulation,[],[f623,f144])).
% 1.69/0.61  fof(f144,plain,(
% 1.69/0.61    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(sK5,sK8(sK5)) | spl11_3),
% 1.69/0.61    inference(resolution,[],[f66,f112])).
% 1.69/0.61  fof(f66,plain,(
% 1.69/0.61    ( ! [X0] : (sP0(X0) | k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0))) )),
% 1.69/0.61    inference(cnf_transformation,[],[f41])).
% 1.69/0.61  fof(f623,plain,(
% 1.69/0.61    k1_funct_1(sK5,sK8(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6)) | (spl11_3 | ~spl11_21)),
% 1.69/0.61    inference(subsumption_resolution,[],[f620,f53])).
% 1.69/0.61  fof(f620,plain,(
% 1.69/0.61    k1_funct_1(sK5,sK8(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6)) | ~v1_relat_1(sK5) | (spl11_3 | ~spl11_21)),
% 1.69/0.61    inference(resolution,[],[f585,f54])).
% 1.69/0.61  fof(f585,plain,(
% 1.69/0.61    ( ! [X0] : (~v1_funct_1(X0) | k1_funct_1(k5_relat_1(sK6,X0),sK10(sK8(sK5),sK6)) = k1_funct_1(X0,sK8(sK5)) | ~v1_relat_1(X0)) ) | (spl11_3 | ~spl11_21)),
% 1.69/0.61    inference(forward_demodulation,[],[f584,f139])).
% 1.69/0.61  fof(f584,plain,(
% 1.69/0.61    ( ! [X0] : (k1_funct_1(k5_relat_1(sK6,X0),sK10(sK8(sK5),sK6)) = k1_funct_1(X0,k1_funct_1(sK6,sK10(sK8(sK5),sK6))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl11_21),
% 1.69/0.61    inference(subsumption_resolution,[],[f583,f55])).
% 1.69/0.61  fof(f583,plain,(
% 1.69/0.61    ( ! [X0] : (k1_funct_1(k5_relat_1(sK6,X0),sK10(sK8(sK5),sK6)) = k1_funct_1(X0,k1_funct_1(sK6,sK10(sK8(sK5),sK6))) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK6)) ) | ~spl11_21),
% 1.69/0.61    inference(subsumption_resolution,[],[f579,f56])).
% 1.69/0.61  fof(f579,plain,(
% 1.69/0.61    ( ! [X0] : (k1_funct_1(k5_relat_1(sK6,X0),sK10(sK8(sK5),sK6)) = k1_funct_1(X0,k1_funct_1(sK6,sK10(sK8(sK5),sK6))) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) ) | ~spl11_21),
% 1.69/0.61    inference(resolution,[],[f544,f82])).
% 1.69/0.61  fof(f82,plain,(
% 1.69/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f24])).
% 1.69/0.61  fof(f24,plain,(
% 1.69/0.61    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.69/0.61    inference(flattening,[],[f23])).
% 1.69/0.61  fof(f23,plain,(
% 1.69/0.61    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.69/0.61    inference(ennf_transformation,[],[f7])).
% 1.69/0.61  fof(f7,axiom,(
% 1.69/0.61    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 1.69/0.61  fof(f600,plain,(
% 1.69/0.61    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | ~r2_hidden(X0,k1_relat_1(sK6)) | sK10(sK7(sK5),sK6) = X0) ) | (spl11_3 | ~spl11_6 | ~spl11_18)),
% 1.69/0.61    inference(forward_demodulation,[],[f599,f212])).
% 1.69/0.61  fof(f212,plain,(
% 1.69/0.61    k1_relat_1(sK6) = k1_relat_1(k5_relat_1(sK6,sK5))),
% 1.69/0.61    inference(subsumption_resolution,[],[f211,f55])).
% 1.69/0.61  fof(f211,plain,(
% 1.69/0.61    k1_relat_1(sK6) = k1_relat_1(k5_relat_1(sK6,sK5)) | ~v1_relat_1(sK6)),
% 1.69/0.61    inference(resolution,[],[f210,f89])).
% 1.69/0.61  fof(f89,plain,(
% 1.69/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.69/0.61    inference(equality_resolution,[],[f85])).
% 1.69/0.61  fof(f85,plain,(
% 1.69/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.69/0.61    inference(cnf_transformation,[],[f52])).
% 1.69/0.61  fof(f52,plain,(
% 1.69/0.61    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.61    inference(flattening,[],[f51])).
% 1.69/0.61  fof(f51,plain,(
% 1.69/0.61    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.61    inference(nnf_transformation,[],[f1])).
% 1.69/0.61  fof(f1,axiom,(
% 1.69/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.69/0.61  fof(f210,plain,(
% 1.69/0.61    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK5)) | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(subsumption_resolution,[],[f209,f53])).
% 1.69/0.61  fof(f209,plain,(
% 1.69/0.61    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK5)) | ~v1_relat_1(sK5) | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(superposition,[],[f60,f58])).
% 1.69/0.61  fof(f60,plain,(
% 1.69/0.61    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f14])).
% 1.69/0.61  fof(f14,plain,(
% 1.69/0.61    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.69/0.61    inference(flattening,[],[f13])).
% 1.69/0.61  fof(f13,plain,(
% 1.69/0.61    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.69/0.61    inference(ennf_transformation,[],[f3])).
% 1.69/0.61  fof(f3,axiom,(
% 1.69/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 1.69/0.61  fof(f599,plain,(
% 1.69/0.61    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK7(sK5),sK6) = X0 | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))) ) | (spl11_3 | ~spl11_6 | ~spl11_18)),
% 1.69/0.61    inference(subsumption_resolution,[],[f598,f518])).
% 1.69/0.61  fof(f518,plain,(
% 1.69/0.61    r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) | ~spl11_18),
% 1.69/0.61    inference(avatar_component_clause,[],[f517])).
% 1.69/0.61  fof(f517,plain,(
% 1.69/0.61    spl11_18 <=> r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))),
% 1.69/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 1.69/0.61  fof(f598,plain,(
% 1.69/0.61    ( ! [X0] : (~r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) | k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK7(sK5),sK6) = X0 | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))) ) | (spl11_3 | ~spl11_6 | ~spl11_18)),
% 1.69/0.61    inference(forward_demodulation,[],[f597,f212])).
% 1.69/0.61  fof(f597,plain,(
% 1.69/0.61    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK7(sK5),sK6) = X0 | ~r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))) ) | (spl11_3 | ~spl11_6 | ~spl11_18)),
% 1.69/0.61    inference(subsumption_resolution,[],[f594,f221])).
% 1.69/0.61  fof(f221,plain,(
% 1.69/0.61    sP0(k5_relat_1(sK6,sK5)) | ~spl11_6),
% 1.69/0.61    inference(avatar_component_clause,[],[f219])).
% 1.69/0.61  fof(f594,plain,(
% 1.69/0.61    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK7(sK5),sK6) = X0 | ~r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) | ~sP0(k5_relat_1(sK6,sK5))) ) | (spl11_3 | ~spl11_18)),
% 1.69/0.61    inference(superposition,[],[f63,f590])).
% 1.69/0.61  fof(f590,plain,(
% 1.69/0.61    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6)) | (spl11_3 | ~spl11_18)),
% 1.69/0.61    inference(subsumption_resolution,[],[f587,f53])).
% 1.69/0.61  fof(f587,plain,(
% 1.69/0.61    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6)) | ~v1_relat_1(sK5) | (spl11_3 | ~spl11_18)),
% 1.69/0.61    inference(resolution,[],[f570,f54])).
% 1.69/0.61  fof(f570,plain,(
% 1.69/0.61    ( ! [X19] : (~v1_funct_1(X19) | k1_funct_1(k5_relat_1(sK6,X19),sK10(sK7(sK5),sK6)) = k1_funct_1(X19,sK7(sK5)) | ~v1_relat_1(X19)) ) | (spl11_3 | ~spl11_18)),
% 1.69/0.61    inference(forward_demodulation,[],[f569,f138])).
% 1.69/0.61  fof(f569,plain,(
% 1.69/0.61    ( ! [X19] : (k1_funct_1(k5_relat_1(sK6,X19),sK10(sK7(sK5),sK6)) = k1_funct_1(X19,k1_funct_1(sK6,sK10(sK7(sK5),sK6))) | ~v1_funct_1(X19) | ~v1_relat_1(X19)) ) | ~spl11_18),
% 1.69/0.61    inference(subsumption_resolution,[],[f568,f55])).
% 1.69/0.61  fof(f568,plain,(
% 1.69/0.61    ( ! [X19] : (k1_funct_1(k5_relat_1(sK6,X19),sK10(sK7(sK5),sK6)) = k1_funct_1(X19,k1_funct_1(sK6,sK10(sK7(sK5),sK6))) | ~v1_funct_1(X19) | ~v1_relat_1(X19) | ~v1_relat_1(sK6)) ) | ~spl11_18),
% 1.69/0.61    inference(subsumption_resolution,[],[f562,f56])).
% 1.69/0.61  fof(f562,plain,(
% 1.69/0.61    ( ! [X19] : (k1_funct_1(k5_relat_1(sK6,X19),sK10(sK7(sK5),sK6)) = k1_funct_1(X19,k1_funct_1(sK6,sK10(sK7(sK5),sK6))) | ~v1_funct_1(X19) | ~v1_relat_1(X19) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) ) | ~spl11_18),
% 1.69/0.61    inference(resolution,[],[f82,f518])).
% 1.69/0.61  fof(f63,plain,(
% 1.69/0.61    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~sP0(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f41])).
% 1.69/0.61  fof(f139,plain,(
% 1.69/0.61    sK8(sK5) = k1_funct_1(sK6,sK10(sK8(sK5),sK6)) | spl11_3),
% 1.69/0.61    inference(resolution,[],[f77,f133])).
% 1.69/0.61  fof(f133,plain,(
% 1.69/0.61    sP2(sK8(sK5),sK6) | spl11_3),
% 1.69/0.61    inference(subsumption_resolution,[],[f130,f118])).
% 1.69/0.61  fof(f130,plain,(
% 1.69/0.61    sP2(sK8(sK5),sK6) | ~sP4(sK6) | spl11_3),
% 1.69/0.61    inference(resolution,[],[f125,f122])).
% 1.69/0.61  fof(f122,plain,(
% 1.69/0.61    r2_hidden(sK8(sK5),k2_relat_1(sK6)) | spl11_3),
% 1.69/0.61    inference(subsumption_resolution,[],[f121,f112])).
% 1.69/0.61  fof(f121,plain,(
% 1.69/0.61    r2_hidden(sK8(sK5),k2_relat_1(sK6)) | sP0(sK5)),
% 1.69/0.61    inference(superposition,[],[f65,f58])).
% 1.69/0.61  fof(f65,plain,(
% 1.69/0.61    ( ! [X0] : (r2_hidden(sK8(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f41])).
% 1.69/0.61  fof(f67,plain,(
% 1.69/0.61    ( ! [X0] : (sK7(X0) != sK8(X0) | sP0(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f41])).
% 1.69/0.61  fof(f553,plain,(
% 1.69/0.61    spl11_3 | spl11_21),
% 1.69/0.61    inference(avatar_contradiction_clause,[],[f552])).
% 1.69/0.61  fof(f552,plain,(
% 1.69/0.61    $false | (spl11_3 | spl11_21)),
% 1.69/0.61    inference(subsumption_resolution,[],[f551,f133])).
% 1.69/0.61  fof(f551,plain,(
% 1.69/0.61    ~sP2(sK8(sK5),sK6) | spl11_21),
% 1.69/0.61    inference(resolution,[],[f545,f76])).
% 1.69/0.61  fof(f76,plain,(
% 1.69/0.61    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1),k1_relat_1(X1)) | ~sP2(X0,X1)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f50])).
% 1.69/0.61  fof(f545,plain,(
% 1.69/0.61    ~r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) | spl11_21),
% 1.69/0.61    inference(avatar_component_clause,[],[f543])).
% 1.69/0.61  fof(f526,plain,(
% 1.69/0.61    spl11_3 | spl11_18),
% 1.69/0.61    inference(avatar_contradiction_clause,[],[f525])).
% 1.69/0.61  fof(f525,plain,(
% 1.69/0.61    $false | (spl11_3 | spl11_18)),
% 1.69/0.61    inference(subsumption_resolution,[],[f524,f132])).
% 1.69/0.61  fof(f524,plain,(
% 1.69/0.61    ~sP2(sK7(sK5),sK6) | spl11_18),
% 1.69/0.61    inference(resolution,[],[f519,f76])).
% 1.69/0.61  fof(f519,plain,(
% 1.69/0.61    ~r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) | spl11_18),
% 1.69/0.61    inference(avatar_component_clause,[],[f517])).
% 1.69/0.61  fof(f242,plain,(
% 1.69/0.61    spl11_1),
% 1.69/0.61    inference(avatar_contradiction_clause,[],[f241])).
% 1.69/0.61  fof(f241,plain,(
% 1.69/0.61    $false | spl11_1),
% 1.69/0.61    inference(subsumption_resolution,[],[f240,f55])).
% 1.69/0.61  fof(f240,plain,(
% 1.69/0.61    ~v1_relat_1(sK6) | spl11_1),
% 1.69/0.61    inference(subsumption_resolution,[],[f239,f56])).
% 1.69/0.61  fof(f239,plain,(
% 1.69/0.61    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl11_1),
% 1.69/0.61    inference(subsumption_resolution,[],[f238,f57])).
% 1.69/0.61  fof(f238,plain,(
% 1.69/0.61    ~v2_funct_1(k5_relat_1(sK6,sK5)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl11_1),
% 1.69/0.61    inference(subsumption_resolution,[],[f237,f94])).
% 1.69/0.61  fof(f94,plain,(
% 1.69/0.61    ~v2_funct_1(sK6) | spl11_1),
% 1.69/0.61    inference(avatar_component_clause,[],[f92])).
% 1.69/0.61  fof(f92,plain,(
% 1.69/0.61    spl11_1 <=> v2_funct_1(sK6)),
% 1.69/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.69/0.61  fof(f237,plain,(
% 1.69/0.61    v2_funct_1(sK6) | ~v2_funct_1(k5_relat_1(sK6,sK5)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)),
% 1.69/0.61    inference(resolution,[],[f236,f89])).
% 1.69/0.61  fof(f236,plain,(
% 1.69/0.61    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(subsumption_resolution,[],[f235,f53])).
% 1.69/0.61  fof(f235,plain,(
% 1.69/0.61    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK5)) )),
% 1.69/0.61    inference(subsumption_resolution,[],[f233,f54])).
% 1.69/0.61  fof(f233,plain,(
% 1.69/0.61    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 1.69/0.61    inference(superposition,[],[f69,f58])).
% 1.69/0.61  fof(f69,plain,(
% 1.69/0.61    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f18])).
% 1.69/0.61  fof(f18,plain,(
% 1.69/0.61    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.61    inference(flattening,[],[f17])).
% 1.69/0.61  fof(f17,plain,(
% 1.69/0.61    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.61    inference(ennf_transformation,[],[f8])).
% 1.69/0.61  fof(f8,axiom,(
% 1.69/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 1.69/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).
% 1.69/0.61  fof(f113,plain,(
% 1.69/0.61    spl11_2 | ~spl11_3),
% 1.69/0.61    inference(avatar_split_clause,[],[f104,f110,f96])).
% 1.69/0.61  fof(f96,plain,(
% 1.69/0.61    spl11_2 <=> v2_funct_1(sK5)),
% 1.69/0.61    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.69/0.61  fof(f104,plain,(
% 1.69/0.61    ~sP0(sK5) | v2_funct_1(sK5)),
% 1.69/0.61    inference(resolution,[],[f102,f62])).
% 1.69/0.61  fof(f62,plain,(
% 1.69/0.61    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 1.69/0.61    inference(cnf_transformation,[],[f37])).
% 1.69/0.61  fof(f102,plain,(
% 1.69/0.61    sP1(sK5)),
% 1.69/0.61    inference(subsumption_resolution,[],[f100,f53])).
% 1.69/0.61  fof(f100,plain,(
% 1.69/0.61    sP1(sK5) | ~v1_relat_1(sK5)),
% 1.69/0.61    inference(resolution,[],[f68,f54])).
% 1.69/0.61  fof(f99,plain,(
% 1.69/0.61    ~spl11_1 | ~spl11_2),
% 1.69/0.61    inference(avatar_split_clause,[],[f59,f96,f92])).
% 1.69/0.61  fof(f59,plain,(
% 1.69/0.61    ~v2_funct_1(sK5) | ~v2_funct_1(sK6)),
% 1.69/0.61    inference(cnf_transformation,[],[f36])).
% 1.69/0.61  % SZS output end Proof for theBenchmark
% 1.69/0.61  % (27469)------------------------------
% 1.69/0.61  % (27469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.61  % (27469)Termination reason: Refutation
% 1.69/0.61  
% 1.69/0.61  % (27469)Memory used [KB]: 11385
% 1.69/0.61  % (27469)Time elapsed: 0.209 s
% 1.69/0.61  % (27469)------------------------------
% 1.69/0.61  % (27469)------------------------------
% 1.69/0.62  % (27443)Success in time 0.26 s
%------------------------------------------------------------------------------
