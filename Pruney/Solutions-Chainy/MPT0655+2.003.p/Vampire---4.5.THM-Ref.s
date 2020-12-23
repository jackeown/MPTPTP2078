%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 154 expanded)
%              Number of leaves         :   13 (  40 expanded)
%              Depth                    :   20
%              Number of atoms          :  380 ( 824 expanded)
%              Number of equality atoms :   84 ( 190 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f408,plain,(
    $false ),
    inference(subsumption_resolution,[],[f407,f46])).

fof(f46,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v2_funct_1(k2_funct_1(sK6))
    & v2_funct_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f8,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(k2_funct_1(X0))
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(k2_funct_1(sK6))
      & v2_funct_1(sK6)
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ~ v2_funct_1(k2_funct_1(X0))
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => v2_funct_1(k2_funct_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f407,plain,(
    ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f406,f47])).

fof(f47,plain,(
    v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f406,plain,
    ( ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6) ),
    inference(subsumption_resolution,[],[f404,f45])).

fof(f45,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f404,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v2_funct_1(sK6)
    | ~ v1_funct_1(sK6) ),
    inference(resolution,[],[f403,f48])).

fof(f48,plain,(
    ~ v2_funct_1(k2_funct_1(sK6)) ),
    inference(cnf_transformation,[],[f26])).

fof(f403,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f402,f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f402,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(k2_funct_1(X0))
      | v2_funct_1(k2_funct_1(X0)) ) ),
    inference(subsumption_resolution,[],[f400,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f400,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | v2_funct_1(k2_funct_1(X0)) ) ),
    inference(resolution,[],[f396,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ sP4(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0) ) ),
    inference(resolution,[],[f77,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ sP5(X0)
      | ~ sP4(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ~ sP4(X0) )
        & ( sP4(X0)
          | ~ v2_funct_1(X0) ) )
      | ~ sP5(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> sP4(X0) )
      | ~ sP5(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f77,plain,(
    ! [X0] :
      ( sP5(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( sP5(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f16,f23,f22])).

fof(f22,plain,(
    ! [X0] :
      ( sP4(X0)
    <=> ! [X1,X2] :
          ( X1 = X2
          | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          | ~ r2_hidden(X2,k1_relat_1(X0))
          | ~ r2_hidden(X1,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f396,plain,(
    ! [X0] :
      ( sP4(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0) ) ),
    inference(resolution,[],[f385,f153])).

fof(f153,plain,(
    ! [X0] :
      ( sP2(X0,k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f152,f49])).

fof(f152,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP2(X0,k2_funct_1(X0)) ) ),
    inference(subsumption_resolution,[],[f146,f50])).

fof(f146,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP2(X0,k2_funct_1(X0)) ) ),
    inference(resolution,[],[f69,f78])).

fof(f78,plain,(
    ! [X1] :
      ( ~ sP3(k2_funct_1(X1),X1)
      | sP2(X1,k2_funct_1(X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | k2_funct_1(X1) != X0
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k2_funct_1(X1) = X0
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | k2_funct_1(X1) != X0 ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ( ( k2_funct_1(X0) = X1
          | ~ sP2(X0,X1) )
        & ( sP2(X0,X1)
          | k2_funct_1(X0) != X1 ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ( k2_funct_1(X0) = X1
      <=> sP2(X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X1,X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f14,f20,f19,f18,f17])).

fof(f17,plain,(
    ! [X2,X3,X0,X1] :
      ( sP0(X2,X3,X0,X1)
    <=> ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X3,X2,X1,X0] :
      ( sP1(X3,X2,X1,X0)
    <=> ( ( k1_funct_1(X1,X2) = X3
          & r2_hidden(X2,k2_relat_1(X0)) )
        | k1_funct_1(X0,X3) != X2
        | ~ r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f19,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1)
    <=> ( ! [X2,X3] :
            ( sP1(X3,X2,X1,X0)
            & sP0(X2,X3,X0,X1) )
        & k1_relat_1(X1) = k2_relat_1(X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

fof(f385,plain,(
    ! [X4,X5] :
      ( ~ sP2(X4,X5)
      | sP4(X5) ) ),
    inference(subsumption_resolution,[],[f384,f90])).

fof(f90,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK9(X2),k2_relat_1(X3))
      | sP4(X2)
      | ~ sP2(X3,X2) ) ),
    inference(superposition,[],[f73,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k2_relat_1(X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ~ sP1(sK8(X0,X1),sK7(X0,X1),X1,X0)
        | ~ sP0(sK7(X0,X1),sK8(X0,X1),X0,X1)
        | k1_relat_1(X1) != k2_relat_1(X0) )
      & ( ( ! [X4,X5] :
              ( sP1(X5,X4,X1,X0)
              & sP0(X4,X5,X0,X1) )
          & k1_relat_1(X1) = k2_relat_1(X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ sP1(X3,X2,X1,X0)
          | ~ sP0(X2,X3,X0,X1) )
     => ( ~ sP1(sK8(X0,X1),sK7(X0,X1),X1,X0)
        | ~ sP0(sK7(X0,X1),sK8(X0,X1),X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2,X3] :
            ( ~ sP1(X3,X2,X1,X0)
            | ~ sP0(X2,X3,X0,X1) )
        | k1_relat_1(X1) != k2_relat_1(X0) )
      & ( ( ! [X4,X5] :
              ( sP1(X5,X4,X1,X0)
              & sP0(X4,X5,X0,X1) )
          & k1_relat_1(X1) = k2_relat_1(X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2,X3] :
            ( ~ sP1(X3,X2,X1,X0)
            | ~ sP0(X2,X3,X0,X1) )
        | k1_relat_1(X1) != k2_relat_1(X0) )
      & ( ( ! [X2,X3] :
              ( sP1(X3,X2,X1,X0)
              & sP0(X2,X3,X0,X1) )
          & k1_relat_1(X1) = k2_relat_1(X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2,X3] :
            ( ~ sP1(X3,X2,X1,X0)
            | ~ sP0(X2,X3,X0,X1) )
        | k1_relat_1(X1) != k2_relat_1(X0) )
      & ( ( ! [X2,X3] :
              ( sP1(X3,X2,X1,X0)
              & sP0(X2,X3,X0,X1) )
          & k1_relat_1(X1) = k2_relat_1(X0) )
        | ~ sP2(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),k1_relat_1(X0))
      | sP4(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( sP4(X0)
        | ( sK9(X0) != sK10(X0)
          & k1_funct_1(X0,sK9(X0)) = k1_funct_1(X0,sK10(X0))
          & r2_hidden(sK10(X0),k1_relat_1(X0))
          & r2_hidden(sK9(X0),k1_relat_1(X0)) ) )
      & ( ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP4(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f42,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK9(X0) != sK10(X0)
        & k1_funct_1(X0,sK9(X0)) = k1_funct_1(X0,sK10(X0))
        & r2_hidden(sK10(X0),k1_relat_1(X0))
        & r2_hidden(sK9(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( sP4(X0)
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
        | ~ sP4(X0) ) ) ),
    inference(rectify,[],[f41])).

% (4987)Refutation not found, incomplete strategy% (4987)------------------------------
% (4987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4987)Termination reason: Refutation not found, incomplete strategy

% (4987)Memory used [KB]: 10618
% (4987)Time elapsed: 0.096 s
fof(f41,plain,(
    ! [X0] :
      ( ( sP4(X0)
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
        | ~ sP4(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

% (4987)------------------------------
% (4987)------------------------------
fof(f384,plain,(
    ! [X4,X5] :
      ( ~ sP2(X4,X5)
      | sP4(X5)
      | ~ r2_hidden(sK9(X5),k2_relat_1(X4)) ) ),
    inference(subsumption_resolution,[],[f383,f76])).

fof(f76,plain,(
    ! [X0] :
      ( sK9(X0) != sK10(X0)
      | sP4(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f383,plain,(
    ! [X4,X5] :
      ( sK9(X5) = sK10(X5)
      | ~ sP2(X4,X5)
      | sP4(X5)
      | ~ r2_hidden(sK9(X5),k2_relat_1(X4)) ) ),
    inference(duplicate_literal_removal,[],[f362])).

fof(f362,plain,(
    ! [X4,X5] :
      ( sK9(X5) = sK10(X5)
      | ~ sP2(X4,X5)
      | sP4(X5)
      | ~ r2_hidden(sK9(X5),k2_relat_1(X4))
      | ~ sP2(X4,X5) ) ),
    inference(superposition,[],[f311,f290])).

fof(f290,plain,(
    ! [X6,X8,X7] :
      ( k1_funct_1(X7,k1_funct_1(X8,X6)) = X6
      | ~ r2_hidden(X6,k2_relat_1(X7))
      | ~ sP2(X7,X8) ) ),
    inference(resolution,[],[f83,f56])).

fof(f56,plain,(
    ! [X4,X0,X5,X1] :
      ( sP0(X4,X5,X0,X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
    ! [X2,X0,X3] :
      ( ~ sP0(X0,k1_funct_1(X3,X0),X2,X3)
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | k1_funct_1(X2,k1_funct_1(X3,X0)) = X0 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X1) = X0
      | k1_funct_1(X3,X0) != X1
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( k1_funct_1(X2,X1) != X0
            | ~ r2_hidden(X1,k1_relat_1(X2)) )
          & k1_funct_1(X3,X0) = X1
          & r2_hidden(X0,k2_relat_1(X2)) ) )
      & ( ( k1_funct_1(X2,X1) = X0
          & r2_hidden(X1,k1_relat_1(X2)) )
        | k1_funct_1(X3,X0) != X1
        | ~ r2_hidden(X0,k2_relat_1(X2))
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X2,X3,X0,X1] :
      ( ( sP0(X2,X3,X0,X1)
        | ( ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
          & k1_funct_1(X1,X2) = X3
          & r2_hidden(X2,k2_relat_1(X0)) ) )
      & ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0))
        | ~ sP0(X2,X3,X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X2,X3,X0,X1] :
      ( ( sP0(X2,X3,X0,X1)
        | ( ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
          & k1_funct_1(X1,X2) = X3
          & r2_hidden(X2,k2_relat_1(X0)) ) )
      & ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0))
        | ~ sP0(X2,X3,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f311,plain,(
    ! [X0,X1] :
      ( sK10(X0) = k1_funct_1(X1,k1_funct_1(X0,sK9(X0)))
      | ~ sP2(X1,X0)
      | sP4(X0) ) ),
    inference(subsumption_resolution,[],[f295,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0),k2_relat_1(X1))
      | sP4(X0)
      | ~ sP2(X1,X0) ) ),
    inference(superposition,[],[f74,f55])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(sK10(X0),k1_relat_1(X0))
      | sP4(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f295,plain,(
    ! [X0,X1] :
      ( sK10(X0) = k1_funct_1(X1,k1_funct_1(X0,sK9(X0)))
      | ~ r2_hidden(sK10(X0),k2_relat_1(X1))
      | ~ sP2(X1,X0)
      | sP4(X0) ) ),
    inference(superposition,[],[f290,f75])).

fof(f75,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK9(X0)) = k1_funct_1(X0,sK10(X0))
      | sP4(X0) ) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (4990)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.47  % (5010)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.49  % (4998)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (4988)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (4991)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (4987)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (5004)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (4990)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f408,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f407,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    v1_funct_1(sK6)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ~v2_funct_1(k2_funct_1(sK6)) & v2_funct_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f8,f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v2_funct_1(k2_funct_1(sK6)) & v2_funct_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f8,plain,(
% 0.20/0.50    ? [X0] : (~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f7])).
% 0.20/0.50  fof(f7,plain,(
% 0.20/0.50    ? [X0] : ((~v2_funct_1(k2_funct_1(X0)) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.20/0.50    inference(negated_conjecture,[],[f5])).
% 0.20/0.50  fof(f5,conjecture,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).
% 0.20/0.50  fof(f407,plain,(
% 0.20/0.50    ~v1_funct_1(sK6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f406,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    v2_funct_1(sK6)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f406,plain,(
% 0.20/0.50    ~v2_funct_1(sK6) | ~v1_funct_1(sK6)),
% 0.20/0.50    inference(subsumption_resolution,[],[f404,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    v1_relat_1(sK6)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f404,plain,(
% 0.20/0.50    ~v1_relat_1(sK6) | ~v2_funct_1(sK6) | ~v1_funct_1(sK6)),
% 0.20/0.50    inference(resolution,[],[f403,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ~v2_funct_1(k2_funct_1(sK6))),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f403,plain,(
% 0.20/0.50    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f402,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.50  fof(f402,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(k2_funct_1(X0)) | v2_funct_1(k2_funct_1(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f400,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f400,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | v2_funct_1(k2_funct_1(X0))) )),
% 0.20/0.50    inference(resolution,[],[f396,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X0] : (~sP4(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | v2_funct_1(X0)) )),
% 0.20/0.50    inference(resolution,[],[f77,f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X0] : (~sP5(X0) | ~sP4(X0) | v2_funct_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0] : (((v2_funct_1(X0) | ~sP4(X0)) & (sP4(X0) | ~v2_funct_1(X0))) | ~sP5(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : ((v2_funct_1(X0) <=> sP4(X0)) | ~sP5(X0))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ( ! [X0] : (sP5(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (sP5(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(definition_folding,[],[f16,f23,f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (sP4(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.20/0.50  fof(f396,plain,(
% 0.20/0.50    ( ! [X0] : (sP4(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0)) )),
% 0.20/0.50    inference(resolution,[],[f385,f153])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    ( ! [X0] : (sP2(X0,k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f152,f49])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP2(X0,k2_funct_1(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f146,f50])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | sP2(X0,k2_funct_1(X0))) )),
% 0.20/0.50    inference(resolution,[],[f69,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X1] : (~sP3(k2_funct_1(X1),X1) | sP2(X1,k2_funct_1(X1))) )),
% 0.20/0.50    inference(equality_resolution,[],[f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sP2(X1,X0) | k2_funct_1(X1) != X0 | ~sP3(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1] : (((k2_funct_1(X1) = X0 | ~sP2(X1,X0)) & (sP2(X1,X0) | k2_funct_1(X1) != X0)) | ~sP3(X0,X1))),
% 0.20/0.50    inference(rectify,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X1,X0] : (((k2_funct_1(X0) = X1 | ~sP2(X0,X1)) & (sP2(X0,X1) | k2_funct_1(X0) != X1)) | ~sP3(X1,X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X1,X0] : ((k2_funct_1(X0) = X1 <=> sP2(X0,X1)) | ~sP3(X1,X0))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sP3(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (sP3(X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(definition_folding,[],[f14,f20,f19,f18,f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X2,X3,X0,X1] : (sP0(X2,X3,X0,X1) <=> ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X3,X2,X1,X0] : (sP1(X3,X2,X1,X0) <=> ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1] : (sP2(X0,X1) <=> (! [X2,X3] : (sP1(X3,X2,X1,X0) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).
% 0.20/0.50  fof(f385,plain,(
% 0.20/0.50    ( ! [X4,X5] : (~sP2(X4,X5) | sP4(X5)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f384,f90])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    ( ! [X2,X3] : (r2_hidden(sK9(X2),k2_relat_1(X3)) | sP4(X2) | ~sP2(X3,X2)) )),
% 0.20/0.50    inference(superposition,[],[f73,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_relat_1(X1) = k2_relat_1(X0) | ~sP2(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1] : ((sP2(X0,X1) | (~sP1(sK8(X0,X1),sK7(X0,X1),X1,X0) | ~sP0(sK7(X0,X1),sK8(X0,X1),X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (sP1(X5,X4,X1,X0) & sP0(X4,X5,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | ~sP2(X0,X1)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f31,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2,X3] : (~sP1(X3,X2,X1,X0) | ~sP0(X2,X3,X0,X1)) => (~sP1(sK8(X0,X1),sK7(X0,X1),X1,X0) | ~sP0(sK7(X0,X1),sK8(X0,X1),X0,X1)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1] : ((sP2(X0,X1) | ? [X2,X3] : (~sP1(X3,X2,X1,X0) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X4,X5] : (sP1(X5,X4,X1,X0) & sP0(X4,X5,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | ~sP2(X0,X1)))),
% 0.20/0.50    inference(rectify,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1] : ((sP2(X0,X1) | ? [X2,X3] : (~sP1(X3,X2,X1,X0) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0)) & ((! [X2,X3] : (sP1(X3,X2,X1,X0) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | ~sP2(X0,X1)))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1] : ((sP2(X0,X1) | (? [X2,X3] : (~sP1(X3,X2,X1,X0) | ~sP0(X2,X3,X0,X1)) | k1_relat_1(X1) != k2_relat_1(X0))) & ((! [X2,X3] : (sP1(X3,X2,X1,X0) & sP0(X2,X3,X0,X1)) & k1_relat_1(X1) = k2_relat_1(X0)) | ~sP2(X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f19])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK9(X0),k1_relat_1(X0)) | sP4(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X0] : ((sP4(X0) | (sK9(X0) != sK10(X0) & k1_funct_1(X0,sK9(X0)) = k1_funct_1(X0,sK10(X0)) & r2_hidden(sK10(X0),k1_relat_1(X0)) & r2_hidden(sK9(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP4(X0)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f42,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK9(X0) != sK10(X0) & k1_funct_1(X0,sK9(X0)) = k1_funct_1(X0,sK10(X0)) & r2_hidden(sK10(X0),k1_relat_1(X0)) & r2_hidden(sK9(X0),k1_relat_1(X0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0] : ((sP4(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~sP4(X0)))),
% 0.20/0.50    inference(rectify,[],[f41])).
% 0.20/0.50  % (4987)Refutation not found, incomplete strategy% (4987)------------------------------
% 0.20/0.50  % (4987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (4987)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (4987)Memory used [KB]: 10618
% 0.20/0.50  % (4987)Time elapsed: 0.096 s
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0] : ((sP4(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~sP4(X0)))),
% 0.20/0.50    inference(nnf_transformation,[],[f22])).
% 0.20/0.50  % (4987)------------------------------
% 0.20/0.50  % (4987)------------------------------
% 0.20/0.50  fof(f384,plain,(
% 0.20/0.50    ( ! [X4,X5] : (~sP2(X4,X5) | sP4(X5) | ~r2_hidden(sK9(X5),k2_relat_1(X4))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f383,f76])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X0] : (sK9(X0) != sK10(X0) | sP4(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f383,plain,(
% 0.20/0.50    ( ! [X4,X5] : (sK9(X5) = sK10(X5) | ~sP2(X4,X5) | sP4(X5) | ~r2_hidden(sK9(X5),k2_relat_1(X4))) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f362])).
% 0.20/0.50  fof(f362,plain,(
% 0.20/0.50    ( ! [X4,X5] : (sK9(X5) = sK10(X5) | ~sP2(X4,X5) | sP4(X5) | ~r2_hidden(sK9(X5),k2_relat_1(X4)) | ~sP2(X4,X5)) )),
% 0.20/0.50    inference(superposition,[],[f311,f290])).
% 0.20/0.50  fof(f290,plain,(
% 0.20/0.50    ( ! [X6,X8,X7] : (k1_funct_1(X7,k1_funct_1(X8,X6)) = X6 | ~r2_hidden(X6,k2_relat_1(X7)) | ~sP2(X7,X8)) )),
% 0.20/0.50    inference(resolution,[],[f83,f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X4,X0,X5,X1] : (sP0(X4,X5,X0,X1) | ~sP2(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X2,X0,X3] : (~sP0(X0,k1_funct_1(X3,X0),X2,X3) | ~r2_hidden(X0,k2_relat_1(X2)) | k1_funct_1(X2,k1_funct_1(X3,X0)) = X0) )),
% 0.20/0.50    inference(equality_resolution,[],[f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X1) = X0 | k1_funct_1(X3,X0) != X1 | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,X1,X2,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((k1_funct_1(X2,X1) != X0 | ~r2_hidden(X1,k1_relat_1(X2))) & k1_funct_1(X3,X0) = X1 & r2_hidden(X0,k2_relat_1(X2)))) & ((k1_funct_1(X2,X1) = X0 & r2_hidden(X1,k1_relat_1(X2))) | k1_funct_1(X3,X0) != X1 | ~r2_hidden(X0,k2_relat_1(X2)) | ~sP0(X0,X1,X2,X3)))),
% 0.20/0.50    inference(rectify,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X2,X3,X0,X1] : ((sP0(X2,X3,X0,X1) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)) | ~sP0(X2,X3,X0,X1)))),
% 0.20/0.50    inference(flattening,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X2,X3,X0,X1] : ((sP0(X2,X3,X0,X1) | ((k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))) | ~sP0(X2,X3,X0,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f17])).
% 0.20/0.50  fof(f311,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sK10(X0) = k1_funct_1(X1,k1_funct_1(X0,sK9(X0))) | ~sP2(X1,X0) | sP4(X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f295,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK10(X0),k2_relat_1(X1)) | sP4(X0) | ~sP2(X1,X0)) )),
% 0.20/0.50    inference(superposition,[],[f74,f55])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK10(X0),k1_relat_1(X0)) | sP4(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f295,plain,(
% 0.20/0.50    ( ! [X0,X1] : (sK10(X0) = k1_funct_1(X1,k1_funct_1(X0,sK9(X0))) | ~r2_hidden(sK10(X0),k2_relat_1(X1)) | ~sP2(X1,X0) | sP4(X0)) )),
% 0.20/0.50    inference(superposition,[],[f290,f75])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X0] : (k1_funct_1(X0,sK9(X0)) = k1_funct_1(X0,sK10(X0)) | sP4(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (4990)------------------------------
% 0.20/0.50  % (4990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (4990)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (4990)Memory used [KB]: 6396
% 0.20/0.50  % (4990)Time elapsed: 0.083 s
% 0.20/0.50  % (4990)------------------------------
% 0.20/0.50  % (4990)------------------------------
% 0.20/0.50  % (4984)Success in time 0.149 s
%------------------------------------------------------------------------------
