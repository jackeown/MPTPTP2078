%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:39 EST 2020

% Result     : Theorem 2.13s
% Output     : Refutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 856 expanded)
%              Number of leaves         :   25 ( 271 expanded)
%              Depth                    :   31
%              Number of atoms          :  679 (5499 expanded)
%              Number of equality atoms :  106 ( 898 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f765,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f113,f242,f526,f553,f721,f764])).

fof(f764,plain,(
    spl11_6 ),
    inference(avatar_contradiction_clause,[],[f763])).

fof(f763,plain,
    ( $false
    | spl11_6 ),
    inference(subsumption_resolution,[],[f220,f762])).

fof(f762,plain,(
    sP0(k5_relat_1(sK6,sK5)) ),
    inference(subsumption_resolution,[],[f761,f53])).

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

fof(f761,plain,
    ( ~ v1_relat_1(sK5)
    | sP0(k5_relat_1(sK6,sK5)) ),
    inference(subsumption_resolution,[],[f760,f54])).

fof(f54,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f760,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | sP0(k5_relat_1(sK6,sK5)) ),
    inference(subsumption_resolution,[],[f759,f55])).

fof(f55,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f759,plain,
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

fof(f721,plain,
    ( spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(avatar_contradiction_clause,[],[f720])).

fof(f720,plain,
    ( $false
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f719,f112])).

fof(f112,plain,
    ( ~ sP0(sK5)
    | spl11_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl11_3
  <=> sP0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f719,plain,
    ( sP0(sK5)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(trivial_inequality_removal,[],[f717])).

fof(f717,plain,
    ( sK7(sK5) != sK7(sK5)
    | sP0(sK5)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(superposition,[],[f67,f702])).

fof(f702,plain,
    ( sK7(sK5) = sK8(sK5)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(forward_demodulation,[],[f699,f138])).

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

fof(f699,plain,
    ( sK8(sK5) = k1_funct_1(sK6,sK10(sK7(sK5),sK6))
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(backward_demodulation,[],[f139,f694])).

fof(f694,plain,
    ( sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f692,f544])).

fof(f544,plain,
    ( r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f543])).

fof(f543,plain,
    ( spl11_21
  <=> r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f692,plain,
    ( ~ r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))
    | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(trivial_inequality_removal,[],[f687])).

fof(f687,plain,
    ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(sK5,sK7(sK5))
    | ~ r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))
    | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6)
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_21 ),
    inference(superposition,[],[f597,f586])).

fof(f586,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6))
    | spl11_3
    | ~ spl11_21 ),
    inference(forward_demodulation,[],[f585,f144])).

fof(f144,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(sK5,sK8(sK5))
    | spl11_3 ),
    inference(resolution,[],[f66,f112])).

fof(f66,plain,(
    ! [X0] :
      ( sP0(X0)
      | k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f585,plain,
    ( k1_funct_1(sK5,sK8(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6))
    | spl11_3
    | ~ spl11_21 ),
    inference(forward_demodulation,[],[f581,f139])).

fof(f581,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK6,sK10(sK8(sK5),sK6))) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6))
    | ~ spl11_21 ),
    inference(resolution,[],[f565,f544])).

fof(f565,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | k1_funct_1(sK5,k1_funct_1(sK6,X0)) = k1_funct_1(k5_relat_1(sK6,sK5),X0) ) ),
    inference(subsumption_resolution,[],[f564,f53])).

fof(f564,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | k1_funct_1(sK5,k1_funct_1(sK6,X0)) = k1_funct_1(k5_relat_1(sK6,sK5),X0)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f563,f54])).

fof(f563,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | k1_funct_1(sK5,k1_funct_1(sK6,X0)) = k1_funct_1(k5_relat_1(sK6,sK5),X0)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f562,f55])).

fof(f562,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | k1_funct_1(sK5,k1_funct_1(sK6,X0)) = k1_funct_1(k5_relat_1(sK6,sK5),X0)
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(subsumption_resolution,[],[f561,f56])).

fof(f561,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | k1_funct_1(sK5,k1_funct_1(sK6,X0)) = k1_funct_1(k5_relat_1(sK6,sK5),X0)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6)
      | ~ v1_funct_1(sK5)
      | ~ v1_relat_1(sK5) ) ),
    inference(superposition,[],[f82,f212])).

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

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
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
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f597,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | ~ r2_hidden(X0,k1_relat_1(sK6))
        | sK10(sK7(sK5),sK6) = X0 )
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(forward_demodulation,[],[f596,f212])).

fof(f596,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK7(sK5),sK6) = X0
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) )
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f595,f518])).

fof(f518,plain,
    ( r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f517])).

fof(f517,plain,
    ( spl11_18
  <=> r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f595,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))
        | k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK7(sK5),sK6) = X0
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) )
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(forward_demodulation,[],[f594,f212])).

fof(f594,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK7(sK5),sK6) = X0
        | ~ r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5)))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) )
    | spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f591,f221])).

fof(f221,plain,
    ( sP0(k5_relat_1(sK6,sK5))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f219])).

fof(f591,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0)
        | sK10(sK7(sK5),sK6) = X0
        | ~ r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5)))
        | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))
        | ~ sP0(k5_relat_1(sK6,sK5)) )
    | spl11_3
    | ~ spl11_18 ),
    inference(superposition,[],[f63,f583])).

fof(f583,plain,
    ( k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6))
    | spl11_3
    | ~ spl11_18 ),
    inference(forward_demodulation,[],[f580,f138])).

fof(f580,plain,
    ( k1_funct_1(sK5,k1_funct_1(sK6,sK10(sK7(sK5),sK6))) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6))
    | ~ spl11_18 ),
    inference(resolution,[],[f565,f518])).

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
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:43:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (15171)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  % (15172)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (15176)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (15177)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (15173)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (15165)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.55  % (15166)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.55  % (15183)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.40/0.56  % (15179)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.40/0.56  % (15180)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.40/0.56  % (15184)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.40/0.56  % (15185)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.40/0.56  % (15174)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.40/0.56  % (15168)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.40/0.56  % (15164)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.40/0.56  % (15163)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.40/0.56  % (15169)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.40/0.56  % (15178)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.40/0.56  % (15170)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.40/0.56  % (15167)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.60/0.57  % (15181)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.60/0.58  % (15182)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.60/0.58  % (15161)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.60/0.58  % (15186)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.60/0.59  % (15175)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.60/0.59  % (15162)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 2.13/0.64  % (15186)Refutation found. Thanks to Tanya!
% 2.13/0.64  % SZS status Theorem for theBenchmark
% 2.13/0.65  % SZS output start Proof for theBenchmark
% 2.13/0.66  fof(f765,plain,(
% 2.13/0.66    $false),
% 2.13/0.66    inference(avatar_sat_refutation,[],[f99,f113,f242,f526,f553,f721,f764])).
% 2.13/0.66  fof(f764,plain,(
% 2.13/0.66    spl11_6),
% 2.13/0.66    inference(avatar_contradiction_clause,[],[f763])).
% 2.13/0.66  fof(f763,plain,(
% 2.13/0.66    $false | spl11_6),
% 2.13/0.66    inference(subsumption_resolution,[],[f220,f762])).
% 2.13/0.66  fof(f762,plain,(
% 2.13/0.66    sP0(k5_relat_1(sK6,sK5))),
% 2.13/0.66    inference(subsumption_resolution,[],[f761,f53])).
% 2.13/0.66  fof(f53,plain,(
% 2.13/0.66    v1_relat_1(sK5)),
% 2.13/0.66    inference(cnf_transformation,[],[f36])).
% 2.13/0.66  fof(f36,plain,(
% 2.13/0.66    ((~v2_funct_1(sK5) | ~v2_funct_1(sK6)) & k1_relat_1(sK5) = k2_relat_1(sK6) & v2_funct_1(k5_relat_1(sK6,sK5)) & v1_funct_1(sK6) & v1_relat_1(sK6)) & v1_funct_1(sK5) & v1_relat_1(sK5)),
% 2.13/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f12,f35,f34])).
% 2.13/0.66  fof(f34,plain,(
% 2.13/0.66    ? [X0] : (? [X1] : ((~v2_funct_1(X0) | ~v2_funct_1(X1)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : ((~v2_funct_1(sK5) | ~v2_funct_1(X1)) & k2_relat_1(X1) = k1_relat_1(sK5) & v2_funct_1(k5_relat_1(X1,sK5)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK5) & v1_relat_1(sK5))),
% 2.13/0.66    introduced(choice_axiom,[])).
% 2.13/0.66  fof(f35,plain,(
% 2.13/0.66    ? [X1] : ((~v2_funct_1(sK5) | ~v2_funct_1(X1)) & k2_relat_1(X1) = k1_relat_1(sK5) & v2_funct_1(k5_relat_1(X1,sK5)) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~v2_funct_1(sK5) | ~v2_funct_1(sK6)) & k1_relat_1(sK5) = k2_relat_1(sK6) & v2_funct_1(k5_relat_1(sK6,sK5)) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 2.13/0.66    introduced(choice_axiom,[])).
% 2.13/0.66  fof(f12,plain,(
% 2.13/0.66    ? [X0] : (? [X1] : ((~v2_funct_1(X0) | ~v2_funct_1(X1)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 2.13/0.66    inference(flattening,[],[f11])).
% 2.13/0.66  fof(f11,plain,(
% 2.13/0.66    ? [X0] : (? [X1] : (((~v2_funct_1(X0) | ~v2_funct_1(X1)) & (k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 2.13/0.66    inference(ennf_transformation,[],[f10])).
% 2.13/0.66  fof(f10,negated_conjecture,(
% 2.13/0.66    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.13/0.66    inference(negated_conjecture,[],[f9])).
% 2.13/0.66  fof(f9,conjecture,(
% 2.13/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.13/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 2.13/0.66  fof(f761,plain,(
% 2.13/0.66    ~v1_relat_1(sK5) | sP0(k5_relat_1(sK6,sK5))),
% 2.13/0.66    inference(subsumption_resolution,[],[f760,f54])).
% 2.13/0.66  fof(f54,plain,(
% 2.13/0.66    v1_funct_1(sK5)),
% 2.13/0.66    inference(cnf_transformation,[],[f36])).
% 2.13/0.66  fof(f760,plain,(
% 2.13/0.66    ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | sP0(k5_relat_1(sK6,sK5))),
% 2.13/0.66    inference(subsumption_resolution,[],[f759,f55])).
% 2.13/0.66  fof(f55,plain,(
% 2.13/0.66    v1_relat_1(sK6)),
% 2.13/0.66    inference(cnf_transformation,[],[f36])).
% 2.13/0.66  fof(f759,plain,(
% 2.13/0.66    ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | sP0(k5_relat_1(sK6,sK5))),
% 2.13/0.66    inference(subsumption_resolution,[],[f232,f56])).
% 2.13/0.66  fof(f56,plain,(
% 2.13/0.66    v1_funct_1(sK6)),
% 2.13/0.66    inference(cnf_transformation,[],[f36])).
% 2.13/0.66  fof(f232,plain,(
% 2.13/0.66    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | sP0(k5_relat_1(sK6,sK5))),
% 2.13/0.66    inference(resolution,[],[f170,f57])).
% 2.13/0.66  fof(f57,plain,(
% 2.13/0.66    v2_funct_1(k5_relat_1(sK6,sK5))),
% 2.13/0.66    inference(cnf_transformation,[],[f36])).
% 2.13/0.66  fof(f170,plain,(
% 2.13/0.66    ( ! [X2,X3] : (~v2_funct_1(k5_relat_1(X3,X2)) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | sP0(k5_relat_1(X3,X2))) )),
% 2.13/0.66    inference(resolution,[],[f168,f61])).
% 2.13/0.66  fof(f61,plain,(
% 2.13/0.66    ( ! [X0] : (~sP1(X0) | ~v2_funct_1(X0) | sP0(X0)) )),
% 2.13/0.66    inference(cnf_transformation,[],[f37])).
% 2.13/0.66  fof(f37,plain,(
% 2.13/0.66    ! [X0] : (((v2_funct_1(X0) | ~sP0(X0)) & (sP0(X0) | ~v2_funct_1(X0))) | ~sP1(X0))),
% 2.13/0.66    inference(nnf_transformation,[],[f28])).
% 2.13/0.66  fof(f28,plain,(
% 2.13/0.66    ! [X0] : ((v2_funct_1(X0) <=> sP0(X0)) | ~sP1(X0))),
% 2.13/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.13/0.66  fof(f168,plain,(
% 2.13/0.66    ( ! [X2,X3] : (sP1(k5_relat_1(X3,X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X2)) )),
% 2.13/0.66    inference(subsumption_resolution,[],[f166,f83])).
% 2.30/0.66  fof(f83,plain,(
% 2.30/0.66    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.30/0.66    inference(cnf_transformation,[],[f26])).
% 2.30/0.66  fof(f26,plain,(
% 2.30/0.66    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.30/0.66    inference(flattening,[],[f25])).
% 2.30/0.66  fof(f25,plain,(
% 2.30/0.66    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.30/0.66    inference(ennf_transformation,[],[f2])).
% 2.30/0.66  fof(f2,axiom,(
% 2.30/0.66    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.30/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 2.30/0.66  fof(f166,plain,(
% 2.30/0.66    ( ! [X2,X3] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X3) | ~v1_relat_1(X3) | sP1(k5_relat_1(X3,X2)) | ~v1_relat_1(k5_relat_1(X3,X2))) )),
% 2.30/0.66    inference(resolution,[],[f81,f68])).
% 2.30/0.66  fof(f68,plain,(
% 2.30/0.66    ( ! [X0] : (~v1_funct_1(X0) | sP1(X0) | ~v1_relat_1(X0)) )),
% 2.30/0.66    inference(cnf_transformation,[],[f29])).
% 2.30/0.66  fof(f29,plain,(
% 2.30/0.66    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.30/0.66    inference(definition_folding,[],[f16,f28,f27])).
% 2.30/0.66  fof(f27,plain,(
% 2.30/0.66    ! [X0] : (sP0(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 2.30/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.30/0.66  fof(f16,plain,(
% 2.30/0.66    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.30/0.66    inference(flattening,[],[f15])).
% 2.30/0.66  fof(f15,plain,(
% 2.30/0.66    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.30/0.66    inference(ennf_transformation,[],[f5])).
% 2.30/0.66  fof(f5,axiom,(
% 2.30/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 2.30/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 2.30/0.66  fof(f81,plain,(
% 2.30/0.66    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.30/0.66    inference(cnf_transformation,[],[f22])).
% 2.30/0.66  fof(f22,plain,(
% 2.30/0.66    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.30/0.66    inference(flattening,[],[f21])).
% 2.30/0.66  fof(f21,plain,(
% 2.30/0.66    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.30/0.66    inference(ennf_transformation,[],[f6])).
% 2.30/0.66  fof(f6,axiom,(
% 2.30/0.66    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 2.30/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).
% 2.30/0.66  fof(f220,plain,(
% 2.30/0.66    ~sP0(k5_relat_1(sK6,sK5)) | spl11_6),
% 2.30/0.66    inference(avatar_component_clause,[],[f219])).
% 2.30/0.66  fof(f219,plain,(
% 2.30/0.66    spl11_6 <=> sP0(k5_relat_1(sK6,sK5))),
% 2.30/0.66    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 2.30/0.66  fof(f721,plain,(
% 2.30/0.66    spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21),
% 2.30/0.66    inference(avatar_contradiction_clause,[],[f720])).
% 2.30/0.66  fof(f720,plain,(
% 2.30/0.66    $false | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 2.30/0.66    inference(subsumption_resolution,[],[f719,f112])).
% 2.30/0.66  fof(f112,plain,(
% 2.30/0.66    ~sP0(sK5) | spl11_3),
% 2.30/0.66    inference(avatar_component_clause,[],[f110])).
% 2.30/0.66  fof(f110,plain,(
% 2.30/0.66    spl11_3 <=> sP0(sK5)),
% 2.30/0.66    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 2.30/0.66  fof(f719,plain,(
% 2.30/0.66    sP0(sK5) | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 2.30/0.66    inference(trivial_inequality_removal,[],[f717])).
% 2.30/0.66  fof(f717,plain,(
% 2.30/0.66    sK7(sK5) != sK7(sK5) | sP0(sK5) | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 2.30/0.66    inference(superposition,[],[f67,f702])).
% 2.30/0.66  fof(f702,plain,(
% 2.30/0.66    sK7(sK5) = sK8(sK5) | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 2.30/0.66    inference(forward_demodulation,[],[f699,f138])).
% 2.30/0.66  fof(f138,plain,(
% 2.30/0.66    sK7(sK5) = k1_funct_1(sK6,sK10(sK7(sK5),sK6)) | spl11_3),
% 2.30/0.66    inference(resolution,[],[f77,f132])).
% 2.30/0.66  fof(f132,plain,(
% 2.30/0.66    sP2(sK7(sK5),sK6) | spl11_3),
% 2.30/0.66    inference(subsumption_resolution,[],[f129,f118])).
% 2.30/0.66  fof(f118,plain,(
% 2.30/0.66    sP4(sK6)),
% 2.30/0.66    inference(subsumption_resolution,[],[f116,f55])).
% 2.30/0.66  fof(f116,plain,(
% 2.30/0.66    sP4(sK6) | ~v1_relat_1(sK6)),
% 2.30/0.66    inference(resolution,[],[f79,f56])).
% 2.30/0.66  fof(f79,plain,(
% 2.30/0.66    ( ! [X0] : (~v1_funct_1(X0) | sP4(X0) | ~v1_relat_1(X0)) )),
% 2.30/0.66    inference(cnf_transformation,[],[f33])).
% 2.30/0.66  fof(f33,plain,(
% 2.30/0.66    ! [X0] : (sP4(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.30/0.66    inference(definition_folding,[],[f20,f32,f31,f30])).
% 2.30/0.66  fof(f30,plain,(
% 2.30/0.66    ! [X2,X0] : (sP2(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 2.30/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.30/0.66  fof(f31,plain,(
% 2.30/0.66    ! [X0,X1] : (sP3(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP2(X2,X0)))),
% 2.30/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.30/0.66  fof(f32,plain,(
% 2.30/0.66    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP3(X0,X1)) | ~sP4(X0))),
% 2.30/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 2.30/0.66  fof(f20,plain,(
% 2.30/0.66    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.30/0.66    inference(flattening,[],[f19])).
% 2.30/0.66  fof(f19,plain,(
% 2.30/0.66    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.30/0.66    inference(ennf_transformation,[],[f4])).
% 2.30/0.66  fof(f4,axiom,(
% 2.30/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.30/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 2.30/0.66  fof(f129,plain,(
% 2.30/0.66    sP2(sK7(sK5),sK6) | ~sP4(sK6) | spl11_3),
% 2.30/0.66    inference(resolution,[],[f125,f120])).
% 2.30/0.66  fof(f120,plain,(
% 2.30/0.66    r2_hidden(sK7(sK5),k2_relat_1(sK6)) | spl11_3),
% 2.30/0.66    inference(subsumption_resolution,[],[f119,f112])).
% 2.30/0.66  fof(f119,plain,(
% 2.30/0.66    r2_hidden(sK7(sK5),k2_relat_1(sK6)) | sP0(sK5)),
% 2.30/0.66    inference(superposition,[],[f64,f58])).
% 2.30/0.66  fof(f58,plain,(
% 2.30/0.66    k1_relat_1(sK5) = k2_relat_1(sK6)),
% 2.30/0.66    inference(cnf_transformation,[],[f36])).
% 2.30/0.66  fof(f64,plain,(
% 2.30/0.66    ( ! [X0] : (r2_hidden(sK7(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 2.30/0.66    inference(cnf_transformation,[],[f41])).
% 2.30/0.66  fof(f41,plain,(
% 2.30/0.66    ! [X0] : ((sP0(X0) | (sK7(X0) != sK8(X0) & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) & r2_hidden(sK8(X0),k1_relat_1(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 2.30/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f39,f40])).
% 2.30/0.66  fof(f40,plain,(
% 2.30/0.66    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK7(X0) != sK8(X0) & k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0)) & r2_hidden(sK8(X0),k1_relat_1(X0)) & r2_hidden(sK7(X0),k1_relat_1(X0))))),
% 2.30/0.66    introduced(choice_axiom,[])).
% 2.30/0.66  fof(f39,plain,(
% 2.30/0.66    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X0)))),
% 2.30/0.66    inference(rectify,[],[f38])).
% 2.30/0.66  fof(f38,plain,(
% 2.30/0.66    ! [X0] : ((sP0(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP0(X0)))),
% 2.30/0.66    inference(nnf_transformation,[],[f27])).
% 2.30/0.66  fof(f125,plain,(
% 2.30/0.66    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(X1)) | sP2(X0,X1) | ~sP4(X1)) )),
% 2.30/0.66    inference(resolution,[],[f72,f87])).
% 2.30/0.66  fof(f87,plain,(
% 2.30/0.66    ( ! [X0] : (sP3(X0,k2_relat_1(X0)) | ~sP4(X0)) )),
% 2.30/0.66    inference(equality_resolution,[],[f70])).
% 2.30/0.66  fof(f70,plain,(
% 2.30/0.66    ( ! [X0,X1] : (sP3(X0,X1) | k2_relat_1(X0) != X1 | ~sP4(X0)) )),
% 2.30/0.66    inference(cnf_transformation,[],[f42])).
% 2.30/0.66  fof(f42,plain,(
% 2.30/0.66    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP3(X0,X1)) & (sP3(X0,X1) | k2_relat_1(X0) != X1)) | ~sP4(X0))),
% 2.30/0.66    inference(nnf_transformation,[],[f32])).
% 2.30/0.66  fof(f72,plain,(
% 2.30/0.66    ( ! [X0,X3,X1] : (~sP3(X0,X1) | ~r2_hidden(X3,X1) | sP2(X3,X0)) )),
% 2.30/0.66    inference(cnf_transformation,[],[f46])).
% 2.30/0.66  fof(f46,plain,(
% 2.30/0.66    ! [X0,X1] : ((sP3(X0,X1) | ((~sP2(sK9(X0,X1),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (sP2(sK9(X0,X1),X0) | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP2(X3,X0)) & (sP2(X3,X0) | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 2.30/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f44,f45])).
% 2.30/0.66  fof(f45,plain,(
% 2.30/0.66    ! [X1,X0] : (? [X2] : ((~sP2(X2,X0) | ~r2_hidden(X2,X1)) & (sP2(X2,X0) | r2_hidden(X2,X1))) => ((~sP2(sK9(X0,X1),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (sP2(sK9(X0,X1),X0) | r2_hidden(sK9(X0,X1),X1))))),
% 2.30/0.66    introduced(choice_axiom,[])).
% 2.30/0.66  fof(f44,plain,(
% 2.30/0.66    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((~sP2(X2,X0) | ~r2_hidden(X2,X1)) & (sP2(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP2(X3,X0)) & (sP2(X3,X0) | ~r2_hidden(X3,X1))) | ~sP3(X0,X1)))),
% 2.30/0.66    inference(rectify,[],[f43])).
% 2.30/0.66  fof(f43,plain,(
% 2.30/0.66    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : ((~sP2(X2,X0) | ~r2_hidden(X2,X1)) & (sP2(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP2(X2,X0)) & (sP2(X2,X0) | ~r2_hidden(X2,X1))) | ~sP3(X0,X1)))),
% 2.30/0.66    inference(nnf_transformation,[],[f31])).
% 2.30/0.66  fof(f77,plain,(
% 2.30/0.66    ( ! [X0,X1] : (~sP2(X0,X1) | k1_funct_1(X1,sK10(X0,X1)) = X0) )),
% 2.30/0.66    inference(cnf_transformation,[],[f50])).
% 2.30/0.66  fof(f50,plain,(
% 2.30/0.66    ! [X0,X1] : ((sP2(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK10(X0,X1)) = X0 & r2_hidden(sK10(X0,X1),k1_relat_1(X1))) | ~sP2(X0,X1)))),
% 2.30/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f48,f49])).
% 2.30/0.66  fof(f49,plain,(
% 2.30/0.66    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK10(X0,X1)) = X0 & r2_hidden(sK10(X0,X1),k1_relat_1(X1))))),
% 2.30/0.66    introduced(choice_axiom,[])).
% 2.30/0.66  fof(f48,plain,(
% 2.30/0.66    ! [X0,X1] : ((sP2(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP2(X0,X1)))),
% 2.30/0.66    inference(rectify,[],[f47])).
% 2.30/0.66  fof(f47,plain,(
% 2.30/0.66    ! [X2,X0] : ((sP2(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP2(X2,X0)))),
% 2.30/0.66    inference(nnf_transformation,[],[f30])).
% 2.30/0.66  fof(f699,plain,(
% 2.30/0.66    sK8(sK5) = k1_funct_1(sK6,sK10(sK7(sK5),sK6)) | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 2.30/0.66    inference(backward_demodulation,[],[f139,f694])).
% 2.30/0.66  fof(f694,plain,(
% 2.30/0.66    sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6) | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 2.30/0.66    inference(subsumption_resolution,[],[f692,f544])).
% 2.30/0.66  fof(f544,plain,(
% 2.30/0.66    r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) | ~spl11_21),
% 2.30/0.66    inference(avatar_component_clause,[],[f543])).
% 2.30/0.66  fof(f543,plain,(
% 2.30/0.66    spl11_21 <=> r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6))),
% 2.30/0.66    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).
% 2.30/0.66  fof(f692,plain,(
% 2.30/0.66    ~r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6) | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 2.30/0.66    inference(trivial_inequality_removal,[],[f687])).
% 2.30/0.66  fof(f687,plain,(
% 2.30/0.66    k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(sK5,sK7(sK5)) | ~r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) | sK10(sK7(sK5),sK6) = sK10(sK8(sK5),sK6) | (spl11_3 | ~spl11_6 | ~spl11_18 | ~spl11_21)),
% 2.30/0.66    inference(superposition,[],[f597,f586])).
% 2.30/0.67  fof(f586,plain,(
% 2.30/0.67    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6)) | (spl11_3 | ~spl11_21)),
% 2.30/0.67    inference(forward_demodulation,[],[f585,f144])).
% 2.30/0.67  fof(f144,plain,(
% 2.30/0.67    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(sK5,sK8(sK5)) | spl11_3),
% 2.30/0.67    inference(resolution,[],[f66,f112])).
% 2.30/0.67  fof(f66,plain,(
% 2.30/0.67    ( ! [X0] : (sP0(X0) | k1_funct_1(X0,sK7(X0)) = k1_funct_1(X0,sK8(X0))) )),
% 2.30/0.67    inference(cnf_transformation,[],[f41])).
% 2.30/0.67  fof(f585,plain,(
% 2.30/0.67    k1_funct_1(sK5,sK8(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6)) | (spl11_3 | ~spl11_21)),
% 2.30/0.67    inference(forward_demodulation,[],[f581,f139])).
% 2.30/0.67  fof(f581,plain,(
% 2.30/0.67    k1_funct_1(sK5,k1_funct_1(sK6,sK10(sK8(sK5),sK6))) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK8(sK5),sK6)) | ~spl11_21),
% 2.30/0.67    inference(resolution,[],[f565,f544])).
% 2.30/0.67  fof(f565,plain,(
% 2.30/0.67    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | k1_funct_1(sK5,k1_funct_1(sK6,X0)) = k1_funct_1(k5_relat_1(sK6,sK5),X0)) )),
% 2.30/0.67    inference(subsumption_resolution,[],[f564,f53])).
% 2.30/0.67  fof(f564,plain,(
% 2.30/0.67    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | k1_funct_1(sK5,k1_funct_1(sK6,X0)) = k1_funct_1(k5_relat_1(sK6,sK5),X0) | ~v1_relat_1(sK5)) )),
% 2.30/0.67    inference(subsumption_resolution,[],[f563,f54])).
% 2.30/0.67  fof(f563,plain,(
% 2.30/0.67    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | k1_funct_1(sK5,k1_funct_1(sK6,X0)) = k1_funct_1(k5_relat_1(sK6,sK5),X0) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 2.30/0.67    inference(subsumption_resolution,[],[f562,f55])).
% 2.30/0.67  fof(f562,plain,(
% 2.30/0.67    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | k1_funct_1(sK5,k1_funct_1(sK6,X0)) = k1_funct_1(k5_relat_1(sK6,sK5),X0) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 2.30/0.67    inference(subsumption_resolution,[],[f561,f56])).
% 2.30/0.67  fof(f561,plain,(
% 2.30/0.67    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | k1_funct_1(sK5,k1_funct_1(sK6,X0)) = k1_funct_1(k5_relat_1(sK6,sK5),X0) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 2.30/0.67    inference(superposition,[],[f82,f212])).
% 2.30/0.67  fof(f212,plain,(
% 2.30/0.67    k1_relat_1(sK6) = k1_relat_1(k5_relat_1(sK6,sK5))),
% 2.30/0.67    inference(subsumption_resolution,[],[f211,f55])).
% 2.30/0.67  fof(f211,plain,(
% 2.30/0.67    k1_relat_1(sK6) = k1_relat_1(k5_relat_1(sK6,sK5)) | ~v1_relat_1(sK6)),
% 2.30/0.67    inference(resolution,[],[f210,f89])).
% 2.30/0.67  fof(f89,plain,(
% 2.30/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.30/0.67    inference(equality_resolution,[],[f85])).
% 2.30/0.67  fof(f85,plain,(
% 2.30/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.30/0.67    inference(cnf_transformation,[],[f52])).
% 2.30/0.67  fof(f52,plain,(
% 2.30/0.67    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.30/0.67    inference(flattening,[],[f51])).
% 2.30/0.67  fof(f51,plain,(
% 2.30/0.67    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.30/0.67    inference(nnf_transformation,[],[f1])).
% 2.30/0.67  fof(f1,axiom,(
% 2.30/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.30/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.30/0.67  fof(f210,plain,(
% 2.30/0.67    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK5)) | ~v1_relat_1(X0)) )),
% 2.30/0.67    inference(subsumption_resolution,[],[f209,f53])).
% 2.30/0.67  fof(f209,plain,(
% 2.30/0.67    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,sK5)) | ~v1_relat_1(sK5) | ~v1_relat_1(X0)) )),
% 2.30/0.67    inference(superposition,[],[f60,f58])).
% 2.30/0.67  fof(f60,plain,(
% 2.30/0.67    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f14])).
% 2.30/0.67  fof(f14,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.30/0.67    inference(flattening,[],[f13])).
% 2.30/0.67  fof(f13,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.30/0.67    inference(ennf_transformation,[],[f3])).
% 2.30/0.67  fof(f3,axiom,(
% 2.30/0.67    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 2.30/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).
% 2.30/0.67  fof(f82,plain,(
% 2.30/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f24])).
% 2.30/0.67  fof(f24,plain,(
% 2.30/0.67    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.30/0.67    inference(flattening,[],[f23])).
% 2.30/0.67  fof(f23,plain,(
% 2.30/0.67    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.30/0.67    inference(ennf_transformation,[],[f7])).
% 2.30/0.67  fof(f7,axiom,(
% 2.30/0.67    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 2.30/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 2.30/0.67  fof(f597,plain,(
% 2.30/0.67    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | ~r2_hidden(X0,k1_relat_1(sK6)) | sK10(sK7(sK5),sK6) = X0) ) | (spl11_3 | ~spl11_6 | ~spl11_18)),
% 2.30/0.67    inference(forward_demodulation,[],[f596,f212])).
% 2.30/0.67  fof(f596,plain,(
% 2.30/0.67    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK7(sK5),sK6) = X0 | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))) ) | (spl11_3 | ~spl11_6 | ~spl11_18)),
% 2.30/0.67    inference(subsumption_resolution,[],[f595,f518])).
% 2.30/0.67  fof(f518,plain,(
% 2.30/0.67    r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) | ~spl11_18),
% 2.30/0.67    inference(avatar_component_clause,[],[f517])).
% 2.30/0.67  fof(f517,plain,(
% 2.30/0.67    spl11_18 <=> r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6))),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 2.30/0.67  fof(f595,plain,(
% 2.30/0.67    ( ! [X0] : (~r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) | k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK7(sK5),sK6) = X0 | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))) ) | (spl11_3 | ~spl11_6 | ~spl11_18)),
% 2.30/0.67    inference(forward_demodulation,[],[f594,f212])).
% 2.30/0.67  fof(f594,plain,(
% 2.30/0.67    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK7(sK5),sK6) = X0 | ~r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5)))) ) | (spl11_3 | ~spl11_6 | ~spl11_18)),
% 2.30/0.67    inference(subsumption_resolution,[],[f591,f221])).
% 2.30/0.67  fof(f221,plain,(
% 2.30/0.67    sP0(k5_relat_1(sK6,sK5)) | ~spl11_6),
% 2.30/0.67    inference(avatar_component_clause,[],[f219])).
% 2.30/0.67  fof(f591,plain,(
% 2.30/0.67    ( ! [X0] : (k1_funct_1(sK5,sK7(sK5)) != k1_funct_1(k5_relat_1(sK6,sK5),X0) | sK10(sK7(sK5),sK6) = X0 | ~r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(k5_relat_1(sK6,sK5))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(sK6,sK5))) | ~sP0(k5_relat_1(sK6,sK5))) ) | (spl11_3 | ~spl11_18)),
% 2.30/0.67    inference(superposition,[],[f63,f583])).
% 2.30/0.67  fof(f583,plain,(
% 2.30/0.67    k1_funct_1(sK5,sK7(sK5)) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6)) | (spl11_3 | ~spl11_18)),
% 2.30/0.67    inference(forward_demodulation,[],[f580,f138])).
% 2.30/0.67  fof(f580,plain,(
% 2.30/0.67    k1_funct_1(sK5,k1_funct_1(sK6,sK10(sK7(sK5),sK6))) = k1_funct_1(k5_relat_1(sK6,sK5),sK10(sK7(sK5),sK6)) | ~spl11_18),
% 2.30/0.67    inference(resolution,[],[f565,f518])).
% 2.30/0.67  fof(f63,plain,(
% 2.30/0.67    ( ! [X4,X0,X3] : (k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | X3 = X4 | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~sP0(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f41])).
% 2.30/0.67  fof(f139,plain,(
% 2.30/0.67    sK8(sK5) = k1_funct_1(sK6,sK10(sK8(sK5),sK6)) | spl11_3),
% 2.30/0.67    inference(resolution,[],[f77,f133])).
% 2.30/0.67  fof(f133,plain,(
% 2.30/0.67    sP2(sK8(sK5),sK6) | spl11_3),
% 2.30/0.67    inference(subsumption_resolution,[],[f130,f118])).
% 2.30/0.67  fof(f130,plain,(
% 2.30/0.67    sP2(sK8(sK5),sK6) | ~sP4(sK6) | spl11_3),
% 2.30/0.67    inference(resolution,[],[f125,f122])).
% 2.30/0.67  fof(f122,plain,(
% 2.30/0.67    r2_hidden(sK8(sK5),k2_relat_1(sK6)) | spl11_3),
% 2.30/0.67    inference(subsumption_resolution,[],[f121,f112])).
% 2.30/0.67  fof(f121,plain,(
% 2.30/0.67    r2_hidden(sK8(sK5),k2_relat_1(sK6)) | sP0(sK5)),
% 2.30/0.67    inference(superposition,[],[f65,f58])).
% 2.30/0.67  fof(f65,plain,(
% 2.30/0.67    ( ! [X0] : (r2_hidden(sK8(X0),k1_relat_1(X0)) | sP0(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f41])).
% 2.30/0.67  fof(f67,plain,(
% 2.30/0.67    ( ! [X0] : (sK7(X0) != sK8(X0) | sP0(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f41])).
% 2.30/0.67  fof(f553,plain,(
% 2.30/0.67    spl11_3 | spl11_21),
% 2.30/0.67    inference(avatar_contradiction_clause,[],[f552])).
% 2.30/0.67  fof(f552,plain,(
% 2.30/0.67    $false | (spl11_3 | spl11_21)),
% 2.30/0.67    inference(subsumption_resolution,[],[f551,f133])).
% 2.30/0.67  fof(f551,plain,(
% 2.30/0.67    ~sP2(sK8(sK5),sK6) | spl11_21),
% 2.30/0.67    inference(resolution,[],[f545,f76])).
% 2.30/0.67  fof(f76,plain,(
% 2.30/0.67    ( ! [X0,X1] : (r2_hidden(sK10(X0,X1),k1_relat_1(X1)) | ~sP2(X0,X1)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f50])).
% 2.30/0.67  fof(f545,plain,(
% 2.30/0.67    ~r2_hidden(sK10(sK8(sK5),sK6),k1_relat_1(sK6)) | spl11_21),
% 2.30/0.67    inference(avatar_component_clause,[],[f543])).
% 2.30/0.67  fof(f526,plain,(
% 2.30/0.67    spl11_3 | spl11_18),
% 2.30/0.67    inference(avatar_contradiction_clause,[],[f525])).
% 2.30/0.67  fof(f525,plain,(
% 2.30/0.67    $false | (spl11_3 | spl11_18)),
% 2.30/0.67    inference(subsumption_resolution,[],[f524,f132])).
% 2.30/0.67  fof(f524,plain,(
% 2.30/0.67    ~sP2(sK7(sK5),sK6) | spl11_18),
% 2.30/0.67    inference(resolution,[],[f519,f76])).
% 2.30/0.67  fof(f519,plain,(
% 2.30/0.67    ~r2_hidden(sK10(sK7(sK5),sK6),k1_relat_1(sK6)) | spl11_18),
% 2.30/0.67    inference(avatar_component_clause,[],[f517])).
% 2.30/0.67  fof(f242,plain,(
% 2.30/0.67    spl11_1),
% 2.30/0.67    inference(avatar_contradiction_clause,[],[f241])).
% 2.30/0.67  fof(f241,plain,(
% 2.30/0.67    $false | spl11_1),
% 2.30/0.67    inference(subsumption_resolution,[],[f240,f55])).
% 2.30/0.67  fof(f240,plain,(
% 2.30/0.67    ~v1_relat_1(sK6) | spl11_1),
% 2.30/0.67    inference(subsumption_resolution,[],[f239,f56])).
% 2.30/0.67  fof(f239,plain,(
% 2.30/0.67    ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl11_1),
% 2.30/0.67    inference(subsumption_resolution,[],[f238,f57])).
% 2.30/0.67  fof(f238,plain,(
% 2.30/0.67    ~v2_funct_1(k5_relat_1(sK6,sK5)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | spl11_1),
% 2.30/0.67    inference(subsumption_resolution,[],[f237,f94])).
% 2.30/0.67  fof(f94,plain,(
% 2.30/0.67    ~v2_funct_1(sK6) | spl11_1),
% 2.30/0.67    inference(avatar_component_clause,[],[f92])).
% 2.30/0.67  fof(f92,plain,(
% 2.30/0.67    spl11_1 <=> v2_funct_1(sK6)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 2.30/0.67  fof(f237,plain,(
% 2.30/0.67    v2_funct_1(sK6) | ~v2_funct_1(k5_relat_1(sK6,sK5)) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)),
% 2.30/0.67    inference(resolution,[],[f236,f89])).
% 2.30/0.67  fof(f236,plain,(
% 2.30/0.67    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.30/0.67    inference(subsumption_resolution,[],[f235,f53])).
% 2.30/0.67  fof(f235,plain,(
% 2.30/0.67    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK5)) )),
% 2.30/0.67    inference(subsumption_resolution,[],[f233,f54])).
% 2.30/0.67  fof(f233,plain,(
% 2.30/0.67    ( ! [X0] : (~r1_tarski(k2_relat_1(X0),k2_relat_1(sK6)) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X0,sK5)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK5) | ~v1_relat_1(sK5)) )),
% 2.30/0.67    inference(superposition,[],[f69,f58])).
% 2.30/0.67  fof(f69,plain,(
% 2.30/0.67    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | v2_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f18])).
% 2.30/0.67  fof(f18,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.30/0.67    inference(flattening,[],[f17])).
% 2.30/0.67  fof(f17,plain,(
% 2.30/0.67    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.30/0.67    inference(ennf_transformation,[],[f8])).
% 2.30/0.67  fof(f8,axiom,(
% 2.30/0.67    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 2.30/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).
% 2.30/0.67  fof(f113,plain,(
% 2.30/0.67    spl11_2 | ~spl11_3),
% 2.30/0.67    inference(avatar_split_clause,[],[f104,f110,f96])).
% 2.30/0.67  fof(f96,plain,(
% 2.30/0.67    spl11_2 <=> v2_funct_1(sK5)),
% 2.30/0.67    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 2.30/0.67  fof(f104,plain,(
% 2.30/0.67    ~sP0(sK5) | v2_funct_1(sK5)),
% 2.30/0.67    inference(resolution,[],[f102,f62])).
% 2.30/0.67  fof(f62,plain,(
% 2.30/0.67    ( ! [X0] : (~sP1(X0) | ~sP0(X0) | v2_funct_1(X0)) )),
% 2.30/0.67    inference(cnf_transformation,[],[f37])).
% 2.30/0.67  fof(f102,plain,(
% 2.30/0.67    sP1(sK5)),
% 2.30/0.67    inference(subsumption_resolution,[],[f100,f53])).
% 2.30/0.67  fof(f100,plain,(
% 2.30/0.67    sP1(sK5) | ~v1_relat_1(sK5)),
% 2.30/0.67    inference(resolution,[],[f68,f54])).
% 2.30/0.67  fof(f99,plain,(
% 2.30/0.67    ~spl11_1 | ~spl11_2),
% 2.30/0.67    inference(avatar_split_clause,[],[f59,f96,f92])).
% 2.30/0.67  fof(f59,plain,(
% 2.30/0.67    ~v2_funct_1(sK5) | ~v2_funct_1(sK6)),
% 2.30/0.67    inference(cnf_transformation,[],[f36])).
% 2.30/0.67  % SZS output end Proof for theBenchmark
% 2.30/0.67  % (15186)------------------------------
% 2.30/0.67  % (15186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.67  % (15186)Termination reason: Refutation
% 2.30/0.67  
% 2.30/0.67  % (15186)Memory used [KB]: 11257
% 2.30/0.67  % (15186)Time elapsed: 0.189 s
% 2.30/0.67  % (15186)------------------------------
% 2.30/0.67  % (15186)------------------------------
% 2.30/0.67  % (15160)Success in time 0.299 s
%------------------------------------------------------------------------------
