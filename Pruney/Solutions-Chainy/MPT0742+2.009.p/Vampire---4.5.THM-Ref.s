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
% DateTime   : Thu Dec  3 12:55:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 191 expanded)
%              Number of leaves         :   19 (  57 expanded)
%              Depth                    :   16
%              Number of atoms          :  326 ( 847 expanded)
%              Number of equality atoms :   24 (  72 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f887,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f168,f886])).

fof(f886,plain,
    ( spl9_5
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f885,f138,f135])).

fof(f135,plain,
    ( spl9_5
  <=> ! [X0] : ~ r2_hidden(X0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

% (19504)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f138,plain,
    ( spl9_6
  <=> v3_ordinal1(sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f885,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4)
    | ~ spl9_6 ),
    inference(resolution,[],[f884,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK7(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK7(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f35])).

fof(f35,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK7(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK7(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f884,plain,
    ( ~ r2_hidden(sK7(sK4),sK4)
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f883,f140])).

fof(f140,plain,
    ( v3_ordinal1(sK7(sK4))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f883,plain,
    ( ~ v3_ordinal1(sK7(sK4))
    | ~ r2_hidden(sK7(sK4),sK4) ),
    inference(resolution,[],[f809,f169])).

fof(f169,plain,(
    ! [X2] :
      ( sP0(X2,sK4)
      | ~ r2_hidden(X2,sK4) ) ),
    inference(subsumption_resolution,[],[f51,f120])).

fof(f120,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f117,f48])).

fof(f48,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ! [X2] :
        ( sP0(X2,sK4)
        | ~ r2_hidden(X2,sK4)
        | ~ v3_ordinal1(X2) )
    & k1_xboole_0 != sK4
    & r1_tarski(sK4,sK5)
    & v3_ordinal1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f22,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( sP0(X2,X0)
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1)
        & v3_ordinal1(X1) )
   => ( ! [X2] :
          ( sP0(X2,sK4)
          | ~ r2_hidden(X2,sK4)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != sK4
      & r1_tarski(sK4,sK5)
      & v3_ordinal1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( sP0(X2,X0)
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(definition_folding,[],[f12,f21])).

fof(f21,plain,(
    ! [X2,X0] :
      ( ? [X3] :
          ( ~ r1_ordinal1(X2,X3)
          & r2_hidden(X3,X0)
          & v3_ordinal1(X3) )
      | ~ sP0(X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ~ ( ! [X2] :
                ( v3_ordinal1(X2)
               => ~ ( ! [X3] :
                        ( v3_ordinal1(X3)
                       => ( r2_hidden(X3,X0)
                         => r1_ordinal1(X2,X3) ) )
                    & r2_hidden(X2,X0) ) )
            & k1_xboole_0 != X0
            & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ~ ( ! [X2] :
              ( v3_ordinal1(X2)
             => ~ ( ! [X3] :
                      ( v3_ordinal1(X3)
                     => ( r2_hidden(X3,X0)
                       => r1_ordinal1(X2,X3) ) )
                  & r2_hidden(X2,X0) ) )
          & k1_xboole_0 != X0
          & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_ordinal1)).

fof(f117,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | v3_ordinal1(X0)
      | ~ v3_ordinal1(sK5) ) ),
    inference(resolution,[],[f115,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

% (19481)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f6,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f115,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK5)
      | ~ r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f113,f49])).

fof(f49,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f107,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X1,X3,X0] :
      ( sP1(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f107,plain,(
    ! [X4,X5,X3] :
      ( sP1(X5,X3,X4)
      | ~ r2_hidden(X3,X4)
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f61,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( sP2(X0,X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f70,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] : sP2(X0,X1,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f1,f24,f23])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP1(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(X1,sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sP1(X1,sK8(X0,X1,X2),X0)
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(X1,sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sP1(X1,sK8(X0,X1,X2),X0)
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X1,X3,X0) )
            & ( sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X2] :
      ( sP0(X2,sK4)
      | ~ r2_hidden(X2,sK4)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f809,plain,(
    ! [X0] :
      ( ~ sP0(sK7(X0),X0)
      | ~ v3_ordinal1(sK7(X0)) ) ),
    inference(duplicate_literal_removal,[],[f806])).

fof(f806,plain,(
    ! [X0] :
      ( ~ sP0(sK7(X0),X0)
      | ~ v3_ordinal1(sK7(X0))
      | ~ sP0(sK7(X0),X0) ) ),
    inference(resolution,[],[f95,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_ordinal1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X1)
        & v3_ordinal1(sK3(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_ordinal1(X0,X2)
          & r2_hidden(X2,X1)
          & v3_ordinal1(X2) )
     => ( ~ r1_ordinal1(X0,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X1)
        & v3_ordinal1(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_ordinal1(X0,X2)
          & r2_hidden(X2,X1)
          & v3_ordinal1(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X2,X0] :
      ( ? [X3] :
          ( ~ r1_ordinal1(X2,X3)
          & r2_hidden(X3,X0)
          & v3_ordinal1(X3) )
      | ~ sP0(X2,X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f95,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK3(sK7(X4),X5),X4)
      | ~ sP0(sK7(X4),X5)
      | ~ v3_ordinal1(sK7(X4)) ) ),
    inference(resolution,[],[f86,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK7(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK7(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | ~ v3_ordinal1(X0)
      | ~ sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f85,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(sK3(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | ~ v3_ordinal1(sK3(X0,X1))
      | ~ v3_ordinal1(X0)
      | ~ sP0(X0,X1) ) ),
    inference(resolution,[],[f53,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,sK3(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f168,plain,(
    ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f163,f50])).

fof(f50,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f31])).

fof(f163,plain,
    ( k1_xboole_0 = sK4
    | ~ spl9_5 ),
    inference(resolution,[],[f157,f73])).

fof(f73,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f58,f52])).

% (19502)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

% (19499)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f157,plain,
    ( ! [X6] :
        ( r2_hidden(sK6(X6,sK4),X6)
        | sK4 = X6 )
    | ~ spl9_5 ),
    inference(resolution,[],[f56,f136])).

fof(f136,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK4)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK6(X0,X1),X1)
          | ~ r2_hidden(sK6(X0,X1),X0) )
        & ( r2_hidden(sK6(X0,X1),X1)
          | r2_hidden(sK6(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1),X1)
          | ~ r2_hidden(sK6(X0,X1),X0) )
        & ( r2_hidden(sK6(X0,X1),X1)
          | r2_hidden(sK6(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f141,plain,
    ( spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f131,f138,f135])).

fof(f131,plain,(
    ! [X0] :
      ( v3_ordinal1(sK7(sK4))
      | ~ r2_hidden(X0,sK4) ) ),
    inference(resolution,[],[f120,f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:24:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (19505)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.50  % (19478)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (19486)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (19482)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (19501)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (19494)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (19492)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (19483)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (19493)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (19487)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (19498)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (19485)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (19484)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (19505)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f887,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f141,f168,f886])).
% 0.21/0.53  fof(f886,plain,(
% 0.21/0.53    spl9_5 | ~spl9_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f885,f138,f135])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    spl9_5 <=> ! [X0] : ~r2_hidden(X0,sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.53  % (19504)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    spl9_6 <=> v3_ordinal1(sK7(sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.53  fof(f885,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK4)) ) | ~spl9_6),
% 0.21/0.53    inference(resolution,[],[f884,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK7(X1),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK7(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK7(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f20,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK7(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK7(X1),X1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.53  fof(f884,plain,(
% 0.21/0.53    ~r2_hidden(sK7(sK4),sK4) | ~spl9_6),
% 0.21/0.53    inference(subsumption_resolution,[],[f883,f140])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    v3_ordinal1(sK7(sK4)) | ~spl9_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f138])).
% 0.21/0.53  fof(f883,plain,(
% 0.21/0.53    ~v3_ordinal1(sK7(sK4)) | ~r2_hidden(sK7(sK4),sK4)),
% 0.21/0.53    inference(resolution,[],[f809,f169])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ( ! [X2] : (sP0(X2,sK4) | ~r2_hidden(X2,sK4)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f51,f120])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK4) | v3_ordinal1(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f117,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    v3_ordinal1(sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X2] : (sP0(X2,sK4) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK4 & r1_tarski(sK4,sK5) & v3_ordinal1(sK5)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f22,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ? [X0,X1] : (! [X2] : (sP0(X2,X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1)) => (! [X2] : (sP0(X2,sK4) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK4 & r1_tarski(sK4,sK5) & v3_ordinal1(sK5))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X0,X1] : (! [X2] : (sP0(X2,X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1))),
% 0.21/0.53    inference(definition_folding,[],[f12,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X2,X0] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~sP0(X2,X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1))),
% 0.21/0.53    inference(flattening,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0,X1] : ((! [X2] : ((? [X3] : ((~r1_ordinal1(X2,X3) & r2_hidden(X3,X0)) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0)) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1)) & v3_ordinal1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_ordinal1)).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,sK4) | v3_ordinal1(X0) | ~v3_ordinal1(sK5)) )),
% 0.21/0.53    inference(resolution,[],[f115,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  % (19481)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,sK5) | ~r2_hidden(X0,sK4)) )),
% 0.21/0.53    inference(resolution,[],[f113,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    r1_tarski(sK4,sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 0.21/0.53    inference(resolution,[],[f107,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | r2_hidden(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP1(X0,X1,X2)))),
% 0.21/0.53    inference(rectify,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP1(X1,X3,X0)))),
% 0.21/0.53    inference(flattening,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP1(X1,X3,X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X1,X3,X0] : (sP1(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (sP1(X5,X3,X4) | ~r2_hidden(X3,X4) | ~r1_tarski(X4,X5)) )),
% 0.21/0.53    inference(resolution,[],[f61,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP2(X0,X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(superposition,[],[f70,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP2(X0,X1,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 0.21/0.53    inference(definition_folding,[],[f1,f24,f23])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X1,X3,X0)))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | sP1(X1,X4,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP1(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f38,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP1(X1,sK8(X0,X1,X2),X0) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sP1(X1,sK8(X0,X1,X2),X0) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.53    inference(rectify,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X1,X3,X0)) & (sP1(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.53    inference(nnf_transformation,[],[f24])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2] : (sP0(X2,sK4) | ~r2_hidden(X2,sK4) | ~v3_ordinal1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f809,plain,(
% 0.21/0.53    ( ! [X0] : (~sP0(sK7(X0),X0) | ~v3_ordinal1(sK7(X0))) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f806])).
% 0.21/0.53  fof(f806,plain,(
% 0.21/0.53    ( ! [X0] : (~sP0(sK7(X0),X0) | ~v3_ordinal1(sK7(X0)) | ~sP0(sK7(X0),X0)) )),
% 0.21/0.53    inference(resolution,[],[f95,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | ~sP0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_ordinal1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X1) & v3_ordinal1(sK3(X0,X1))) | ~sP0(X0,X1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (~r1_ordinal1(X0,X2) & r2_hidden(X2,X1) & v3_ordinal1(X2)) => (~r1_ordinal1(X0,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X1) & v3_ordinal1(sK3(X0,X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : (? [X2] : (~r1_ordinal1(X0,X2) & r2_hidden(X2,X1) & v3_ordinal1(X2)) | ~sP0(X0,X1))),
% 0.21/0.54    inference(rectify,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X2,X0] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~sP0(X2,X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f21])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X4,X5] : (~r2_hidden(sK3(sK7(X4),X5),X4) | ~sP0(sK7(X4),X5) | ~v3_ordinal1(sK7(X4))) )),
% 0.21/0.54    inference(resolution,[],[f86,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X0,sK7(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(condensation,[],[f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK7(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | ~v3_ordinal1(X0) | ~sP0(X0,X1)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f85,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v3_ordinal1(sK3(X0,X1)) | ~sP0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | ~v3_ordinal1(sK3(X0,X1)) | ~v3_ordinal1(X0) | ~sP0(X0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f53,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_ordinal1(X0,sK3(X0,X1)) | ~sP0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    ~spl9_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f167])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    $false | ~spl9_5),
% 0.21/0.54    inference(subsumption_resolution,[],[f163,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    k1_xboole_0 != sK4),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    k1_xboole_0 = sK4 | ~spl9_5),
% 0.21/0.54    inference(resolution,[],[f157,f73])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(resolution,[],[f58,f52])).
% 0.21/0.54  % (19502)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  % (19499)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ( ! [X6] : (r2_hidden(sK6(X6,sK4),X6) | sK4 = X6) ) | ~spl9_5),
% 0.21/0.54    inference(resolution,[],[f56,f136])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,sK4)) ) | ~spl9_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f135])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X1) | X0 = X1 | r2_hidden(sK6(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK6(X0,X1),X1) | ~r2_hidden(sK6(X0,X1),X0)) & (r2_hidden(sK6(X0,X1),X1) | r2_hidden(sK6(X0,X1),X0))))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f32,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK6(X0,X1),X1) | ~r2_hidden(sK6(X0,X1),X0)) & (r2_hidden(sK6(X0,X1),X1) | r2_hidden(sK6(X0,X1),X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.21/0.54    inference(nnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    spl9_5 | spl9_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f131,f138,f135])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    ( ! [X0] : (v3_ordinal1(sK7(sK4)) | ~r2_hidden(X0,sK4)) )),
% 0.21/0.54    inference(resolution,[],[f120,f59])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (19505)------------------------------
% 0.21/0.54  % (19505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (19505)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (19505)Memory used [KB]: 6652
% 0.21/0.54  % (19505)Time elapsed: 0.106 s
% 0.21/0.54  % (19505)------------------------------
% 0.21/0.54  % (19505)------------------------------
% 0.21/0.54  % (19506)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (19488)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (19477)Success in time 0.16 s
%------------------------------------------------------------------------------
