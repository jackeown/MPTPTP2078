%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 190 expanded)
%              Number of leaves         :   17 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :  288 ( 870 expanded)
%              Number of equality atoms :   15 (  67 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f107,f113,f160,f175,f249])).

% (25936)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f249,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f244,f169])).

fof(f169,plain,
    ( r2_hidden(sK2(sK3(sK0)),sK0)
    | ~ spl6_1
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f168,f124])).

fof(f124,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_8
  <=> r2_hidden(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f168,plain,
    ( ~ r2_hidden(sK3(sK0),sK0)
    | r2_hidden(sK2(sK3(sK0)),sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f64,f32])).

fof(f32,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | ~ r2_hidden(X2,sK0)
      | r2_hidden(sK2(X2),sK0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ! [X2] :
        ( ( ~ r1_ordinal1(X2,sK2(X2))
          & r2_hidden(sK2(X2),sK0)
          & v3_ordinal1(sK2(X2)) )
        | ~ r2_hidden(X2,sK0)
        | ~ v3_ordinal1(X2) )
    & k1_xboole_0 != sK0
    & r1_tarski(sK0,sK1)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ? [X3] :
                ( ~ r1_ordinal1(X2,X3)
                & r2_hidden(X3,X0)
                & v3_ordinal1(X3) )
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        & k1_xboole_0 != X0
        & r1_tarski(X0,X1)
        & v3_ordinal1(X1) )
   => ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,sK0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,sK0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != sK0
      & r1_tarski(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X2] :
      ( ? [X3] :
          ( ~ r1_ordinal1(X2,X3)
          & r2_hidden(X3,sK0)
          & v3_ordinal1(X3) )
     => ( ~ r1_ordinal1(X2,sK2(X2))
        & r2_hidden(sK2(X2),sK0)
        & v3_ordinal1(sK2(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f64,plain,
    ( v3_ordinal1(sK3(sK0))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_1
  <=> v3_ordinal1(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f244,plain,
    ( ~ r2_hidden(sK2(sK3(sK0)),sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(resolution,[],[f243,f51])).

fof(f51,plain,(
    ! [X3,X1] :
      ( ~ r2_hidden(X3,sK3(X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(condensation,[],[f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK3(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f20])).

fof(f20,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

% (25942)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f243,plain,
    ( r2_hidden(sK2(sK3(sK0)),sK3(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f242,f64])).

fof(f242,plain,
    ( r2_hidden(sK2(sK3(sK0)),sK3(sK0))
    | ~ v3_ordinal1(sK3(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f241,f124])).

fof(f241,plain,
    ( r2_hidden(sK2(sK3(sK0)),sK3(sK0))
    | ~ r2_hidden(sK3(sK0),sK0)
    | ~ v3_ordinal1(sK3(sK0))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f240,f69])).

fof(f69,plain,
    ( v3_ordinal1(sK2(sK3(sK0)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_2
  <=> v3_ordinal1(sK2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f240,plain,
    ( ~ v3_ordinal1(sK2(sK3(sK0)))
    | r2_hidden(sK2(sK3(sK0)),sK3(sK0))
    | ~ r2_hidden(sK3(sK0),sK0)
    | ~ v3_ordinal1(sK3(sK0))
    | ~ spl6_1 ),
    inference(resolution,[],[f167,f33])).

fof(f33,plain,(
    ! [X2] :
      ( ~ r1_ordinal1(X2,sK2(X2))
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f167,plain,
    ( ! [X1] :
        ( r1_ordinal1(sK3(sK0),X1)
        | ~ v3_ordinal1(X1)
        | r2_hidden(X1,sK3(sK0)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f64,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f175,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | ~ spl6_3 ),
    inference(resolution,[],[f72,f87])).

fof(f87,plain,(
    ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f86,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f86,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(resolution,[],[f49,f48])).

fof(f48,plain,(
    ~ sQ5_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f30,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f30,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sQ5_eqProxy(X0,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f39,f47])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f72,plain,
    ( ! [X6] : r1_tarski(sK0,X6)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f71])).

% (25917)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f71,plain,
    ( spl6_3
  <=> ! [X6] : r1_tarski(sK0,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f160,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl6_8 ),
    inference(resolution,[],[f156,f87])).

fof(f156,plain,
    ( ! [X0] : r1_tarski(sK0,X0)
    | spl6_8 ),
    inference(resolution,[],[f125,f53])).

fof(f53,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | r2_hidden(sK3(X2),X2) ) ),
    inference(resolution,[],[f42,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK3(X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f125,plain,
    ( ~ r2_hidden(sK3(sK0),sK0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f113,plain,
    ( spl6_1
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl6_1
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f111,f28])).

fof(f28,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f111,plain,
    ( ~ v3_ordinal1(sK1)
    | spl6_1
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f109,f65])).

fof(f65,plain,
    ( ~ v3_ordinal1(sK3(sK0))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f109,plain,
    ( v3_ordinal1(sK3(sK0))
    | ~ v3_ordinal1(sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f106,f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f5])).

% (25928)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f106,plain,
    ( r2_hidden(sK3(sK0),sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_6
  <=> r2_hidden(sK3(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f107,plain,
    ( spl6_3
    | spl6_6 ),
    inference(avatar_split_clause,[],[f97,f104,f71])).

fof(f97,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0),sK1)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f85,f29])).

fof(f29,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f85,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,X4)
      | r2_hidden(sK3(X3),X4)
      | r1_tarski(X3,X5) ) ),
    inference(resolution,[],[f41,f53])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,
    ( ~ spl6_1
    | spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f61,f71,f67,f63])).

fof(f61,plain,(
    ! [X6] :
      ( r1_tarski(sK0,X6)
      | v3_ordinal1(sK2(sK3(sK0)))
      | ~ v3_ordinal1(sK3(sK0)) ) ),
    inference(resolution,[],[f53,f31])).

fof(f31,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | v3_ordinal1(sK2(X2))
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:34:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (25922)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (25938)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.53  % (25930)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.53  % (25930)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (25914)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (25915)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f250,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f73,f107,f113,f160,f175,f249])).
% 0.22/0.54  % (25936)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  fof(f249,plain,(
% 0.22/0.54    ~spl6_1 | ~spl6_2 | ~spl6_8),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f248])).
% 0.22/0.54  fof(f248,plain,(
% 0.22/0.54    $false | (~spl6_1 | ~spl6_2 | ~spl6_8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f244,f169])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    r2_hidden(sK2(sK3(sK0)),sK0) | (~spl6_1 | ~spl6_8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f168,f124])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    r2_hidden(sK3(sK0),sK0) | ~spl6_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f123])).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    spl6_8 <=> r2_hidden(sK3(sK0),sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK0),sK0) | r2_hidden(sK2(sK3(sK0)),sK0) | ~spl6_1),
% 0.22/0.54    inference(resolution,[],[f64,f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X2] : (~v3_ordinal1(X2) | ~r2_hidden(X2,sK0) | r2_hidden(sK2(X2),sK0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X2] : ((~r1_ordinal1(X2,sK2(X2)) & r2_hidden(sK2(X2),sK0) & v3_ordinal1(sK2(X2))) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1) & v3_ordinal1(sK1)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1)) => (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,sK0) & v3_ordinal1(X3)) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) & k1_xboole_0 != sK0 & r1_tarski(sK0,sK1) & v3_ordinal1(sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,sK0) & v3_ordinal1(X3)) => (~r1_ordinal1(X2,sK2(X2)) & r2_hidden(sK2(X2),sK0) & v3_ordinal1(sK2(X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1))),
% 0.22/0.54    inference(flattening,[],[f9])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ? [X0,X1] : ((! [X2] : ((? [X3] : ((~r1_ordinal1(X2,X3) & r2_hidden(X3,X0)) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0)) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1)) & v3_ordinal1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 0.22/0.54    inference(negated_conjecture,[],[f7])).
% 0.22/0.54  fof(f7,conjecture,(
% 0.22/0.54    ! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_ordinal1)).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    v3_ordinal1(sK3(sK0)) | ~spl6_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f63])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    spl6_1 <=> v3_ordinal1(sK3(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.54  fof(f244,plain,(
% 0.22/0.54    ~r2_hidden(sK2(sK3(sK0)),sK0) | (~spl6_1 | ~spl6_2 | ~spl6_8)),
% 0.22/0.54    inference(resolution,[],[f243,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X3,X1] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1)) )),
% 0.22/0.54    inference(condensation,[],[f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : ((! [X3] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X1),X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) => (! [X3] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1)) & r2_hidden(sK3(X1),X1)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  % (25942)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    r2_hidden(sK2(sK3(sK0)),sK3(sK0)) | (~spl6_1 | ~spl6_2 | ~spl6_8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f242,f64])).
% 0.22/0.54  fof(f242,plain,(
% 0.22/0.54    r2_hidden(sK2(sK3(sK0)),sK3(sK0)) | ~v3_ordinal1(sK3(sK0)) | (~spl6_1 | ~spl6_2 | ~spl6_8)),
% 0.22/0.54    inference(subsumption_resolution,[],[f241,f124])).
% 0.22/0.54  fof(f241,plain,(
% 0.22/0.54    r2_hidden(sK2(sK3(sK0)),sK3(sK0)) | ~r2_hidden(sK3(sK0),sK0) | ~v3_ordinal1(sK3(sK0)) | (~spl6_1 | ~spl6_2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f240,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    v3_ordinal1(sK2(sK3(sK0))) | ~spl6_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    spl6_2 <=> v3_ordinal1(sK2(sK3(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.54  fof(f240,plain,(
% 0.22/0.54    ~v3_ordinal1(sK2(sK3(sK0))) | r2_hidden(sK2(sK3(sK0)),sK3(sK0)) | ~r2_hidden(sK3(sK0),sK0) | ~v3_ordinal1(sK3(sK0)) | ~spl6_1),
% 0.22/0.54    inference(resolution,[],[f167,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X2] : (~r1_ordinal1(X2,sK2(X2)) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    ( ! [X1] : (r1_ordinal1(sK3(sK0),X1) | ~v3_ordinal1(X1) | r2_hidden(X1,sK3(sK0))) ) | ~spl6_1),
% 0.22/0.54    inference(resolution,[],[f64,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | r2_hidden(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(flattening,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    ~spl6_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f172])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    $false | ~spl6_3),
% 0.22/0.54    inference(resolution,[],[f72,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ~r1_tarski(sK0,k1_xboole_0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f86,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ~r1_tarski(sK0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.54    inference(resolution,[],[f49,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ~sQ5_eqProxy(k1_xboole_0,sK0)),
% 0.22/0.54    inference(equality_proxy_replacement,[],[f30,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.54    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    k1_xboole_0 != sK0),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sQ5_eqProxy(X0,X1) | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(equality_proxy_replacement,[],[f39,f47])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X6] : (r1_tarski(sK0,X6)) ) | ~spl6_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f71])).
% 0.22/0.54  % (25917)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    spl6_3 <=> ! [X6] : r1_tarski(sK0,X6)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    spl6_8),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f157])).
% 0.22/0.54  fof(f157,plain,(
% 0.22/0.54    $false | spl6_8),
% 0.22/0.54    inference(resolution,[],[f156,f87])).
% 0.22/0.54  fof(f156,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(sK0,X0)) ) | spl6_8),
% 0.22/0.54    inference(resolution,[],[f125,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ( ! [X2,X3] : (r1_tarski(X2,X3) | r2_hidden(sK3(X2),X2)) )),
% 0.22/0.54    inference(resolution,[],[f42,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK3(X1),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f25,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK0),sK0) | spl6_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f123])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    spl6_1 | ~spl6_6),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f112])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    $false | (spl6_1 | ~spl6_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f111,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    v3_ordinal1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    ~v3_ordinal1(sK1) | (spl6_1 | ~spl6_6)),
% 0.22/0.54    inference(subsumption_resolution,[],[f109,f65])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ~v3_ordinal1(sK3(sK0)) | spl6_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f63])).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    v3_ordinal1(sK3(sK0)) | ~v3_ordinal1(sK1) | ~spl6_6),
% 0.22/0.54    inference(resolution,[],[f106,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.22/0.54    inference(flattening,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  % (25928)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    r2_hidden(sK3(sK0),sK1) | ~spl6_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f104])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    spl6_6 <=> r2_hidden(sK3(sK0),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    spl6_3 | spl6_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f97,f104,f71])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK3(sK0),sK1) | r1_tarski(sK0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f85,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    r1_tarski(sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X4,X5,X3] : (~r1_tarski(X3,X4) | r2_hidden(sK3(X3),X4) | r1_tarski(X3,X5)) )),
% 0.22/0.54    inference(resolution,[],[f41,f53])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ~spl6_1 | spl6_2 | spl6_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f61,f71,f67,f63])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X6] : (r1_tarski(sK0,X6) | v3_ordinal1(sK2(sK3(sK0))) | ~v3_ordinal1(sK3(sK0))) )),
% 0.22/0.54    inference(resolution,[],[f53,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X2] : (~r2_hidden(X2,sK0) | v3_ordinal1(sK2(X2)) | ~v3_ordinal1(X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (25930)------------------------------
% 0.22/0.54  % (25930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (25930)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (25930)Memory used [KB]: 10746
% 0.22/0.54  % (25930)Time elapsed: 0.117 s
% 0.22/0.54  % (25930)------------------------------
% 0.22/0.54  % (25930)------------------------------
% 0.22/0.54  % (25918)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (25912)Success in time 0.181 s
%------------------------------------------------------------------------------
