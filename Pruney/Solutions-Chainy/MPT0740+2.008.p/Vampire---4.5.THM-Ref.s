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
% DateTime   : Thu Dec  3 12:55:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 175 expanded)
%              Number of leaves         :   19 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  314 ( 507 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1237,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f173,f236,f920,f1034,f1236])).

fof(f1236,plain,
    ( spl4_10
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f1235])).

fof(f1235,plain,
    ( $false
    | spl4_10
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f1227,f254])).

fof(f254,plain,
    ( r1_tarski(k3_tarski(sK0),sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl4_14
  <=> r1_tarski(k3_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1227,plain,
    ( ~ r1_tarski(k3_tarski(sK0),sK0)
    | spl4_10 ),
    inference(resolution,[],[f1041,f1037])).

fof(f1037,plain,
    ( ~ r2_hidden(sK1(k3_tarski(sK0)),sK0)
    | spl4_10 ),
    inference(resolution,[],[f1035,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f1035,plain,
    ( ~ r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | spl4_10 ),
    inference(resolution,[],[f220,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK1(X0),X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK1(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f220,plain,
    ( ~ v1_ordinal1(k3_tarski(sK0))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl4_10
  <=> v1_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1041,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(k3_tarski(sK0)),X0)
        | ~ r1_tarski(k3_tarski(sK0),X0) )
    | spl4_10 ),
    inference(resolution,[],[f1036,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f1036,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | spl4_10 ),
    inference(resolution,[],[f220,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1034,plain,
    ( spl4_3
    | spl4_5
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f1033])).

fof(f1033,plain,
    ( $false
    | spl4_3
    | spl4_5
    | ~ spl4_10
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f317,f254])).

fof(f317,plain,
    ( ~ r1_tarski(k3_tarski(sK0),sK0)
    | spl4_3
    | spl4_5
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f316,f161])).

fof(f161,plain,
    ( sK0 != k3_tarski(sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl4_5
  <=> sK0 = k3_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f316,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ r1_tarski(k3_tarski(sK0),sK0)
    | spl4_3
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f301,f153])).

fof(f153,plain,
    ( ~ r2_hidden(k3_tarski(sK0),sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl4_3
  <=> r2_hidden(k3_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f301,plain,
    ( r2_hidden(k3_tarski(sK0),sK0)
    | sK0 = k3_tarski(sK0)
    | ~ r1_tarski(k3_tarski(sK0),sK0)
    | ~ spl4_10 ),
    inference(resolution,[],[f219,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_ordinal1(X0)
      | r2_hidden(X0,sK0)
      | sK0 = X0
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f63,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f63,plain,(
    ! [X0] :
      ( ~ r2_xboole_0(X0,sK0)
      | r2_hidden(X0,sK0)
      | ~ v1_ordinal1(X0) ) ),
    inference(resolution,[],[f44,f42])).

fof(f42,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ v3_ordinal1(k3_tarski(sK0))
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(k3_tarski(X0))
        & v3_ordinal1(X0) )
   => ( ~ v3_ordinal1(k3_tarski(sK0))
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f219,plain,
    ( v1_ordinal1(k3_tarski(sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f218])).

fof(f920,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f919])).

fof(f919,plain,
    ( $false
    | spl4_14 ),
    inference(subsumption_resolution,[],[f918,f785])).

fof(f785,plain,
    ( ~ r1_tarski(sK0,sK2(sK0,sK0))
    | spl4_14 ),
    inference(resolution,[],[f778,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

% (28070)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f778,plain,
    ( r2_hidden(sK2(sK0,sK0),sK0)
    | spl4_14 ),
    inference(resolution,[],[f253,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f253,plain,
    ( ~ r1_tarski(k3_tarski(sK0),sK0)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f252])).

fof(f918,plain,
    ( r1_tarski(sK0,sK2(sK0,sK0))
    | spl4_14 ),
    inference(subsumption_resolution,[],[f913,f789])).

fof(f789,plain,
    ( v3_ordinal1(sK2(sK0,sK0))
    | spl4_14 ),
    inference(subsumption_resolution,[],[f784,f42])).

fof(f784,plain,
    ( v3_ordinal1(sK2(sK0,sK0))
    | ~ v3_ordinal1(sK0)
    | spl4_14 ),
    inference(resolution,[],[f778,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f913,plain,
    ( ~ v3_ordinal1(sK2(sK0,sK0))
    | r1_tarski(sK0,sK2(sK0,sK0))
    | spl4_14 ),
    inference(resolution,[],[f842,f777])).

fof(f777,plain,
    ( ~ r1_tarski(sK2(sK0,sK0),sK0)
    | spl4_14 ),
    inference(resolution,[],[f253,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f842,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK0)
      | ~ v3_ordinal1(X0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f414,f42])).

fof(f414,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X1,X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f413])).

fof(f413,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f186,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f186,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_ordinal1(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f51,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f236,plain,(
    ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f227,f42])).

fof(f227,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f43,f162])).

fof(f162,plain,
    ( sK0 = k3_tarski(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f160])).

fof(f43,plain,(
    ~ v3_ordinal1(k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f173,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f171,f42])).

fof(f171,plain,
    ( ~ v3_ordinal1(sK0)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f169,f43])).

fof(f169,plain,
    ( v3_ordinal1(k3_tarski(sK0))
    | ~ v3_ordinal1(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f154,f48])).

fof(f154,plain,
    ( r2_hidden(k3_tarski(sK0),sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (28049)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.48  % (28073)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.48  % (28065)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.49  % (28057)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (28073)Refutation not found, incomplete strategy% (28073)------------------------------
% 0.21/0.49  % (28073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (28059)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (28046)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (28068)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.50  % (28073)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (28073)Memory used [KB]: 10618
% 0.21/0.50  % (28073)Time elapsed: 0.107 s
% 0.21/0.50  % (28073)------------------------------
% 0.21/0.50  % (28073)------------------------------
% 0.21/0.51  % (28051)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (28069)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (28058)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (28048)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (28061)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (28054)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (28060)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (28052)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (28053)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (28054)Refutation not found, incomplete strategy% (28054)------------------------------
% 0.21/0.52  % (28054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28049)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f1237,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f173,f236,f920,f1034,f1236])).
% 0.21/0.52  fof(f1236,plain,(
% 0.21/0.52    spl4_10 | ~spl4_14),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f1235])).
% 0.21/0.52  fof(f1235,plain,(
% 0.21/0.52    $false | (spl4_10 | ~spl4_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f1227,f254])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    r1_tarski(k3_tarski(sK0),sK0) | ~spl4_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f252])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    spl4_14 <=> r1_tarski(k3_tarski(sK0),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.52  fof(f1227,plain,(
% 0.21/0.52    ~r1_tarski(k3_tarski(sK0),sK0) | spl4_10),
% 0.21/0.52    inference(resolution,[],[f1041,f1037])).
% 0.21/0.52  fof(f1037,plain,(
% 0.21/0.52    ~r2_hidden(sK1(k3_tarski(sK0)),sK0) | spl4_10),
% 0.21/0.52    inference(resolution,[],[f1035,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.52  fof(f1035,plain,(
% 0.21/0.52    ~r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0)) | spl4_10),
% 0.21/0.52    inference(resolution,[],[f220,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0] : (v1_ordinal1(X0) | ~r1_tarski(sK1(X0),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK1(X0),X0) & r2_hidden(sK1(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK1(X0),X0) & r2_hidden(sK1(X0),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.21/0.52    inference(rectify,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    ~v1_ordinal1(k3_tarski(sK0)) | spl4_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f218])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    spl4_10 <=> v1_ordinal1(k3_tarski(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.52  fof(f1041,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK1(k3_tarski(sK0)),X0) | ~r1_tarski(k3_tarski(sK0),X0)) ) | spl4_10),
% 0.21/0.52    inference(resolution,[],[f1036,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f1036,plain,(
% 0.21/0.52    r2_hidden(sK1(k3_tarski(sK0)),k3_tarski(sK0)) | spl4_10),
% 0.21/0.52    inference(resolution,[],[f220,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0] : (v1_ordinal1(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f1034,plain,(
% 0.21/0.52    spl4_3 | spl4_5 | ~spl4_10 | ~spl4_14),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f1033])).
% 0.21/0.52  fof(f1033,plain,(
% 0.21/0.52    $false | (spl4_3 | spl4_5 | ~spl4_10 | ~spl4_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f317,f254])).
% 0.21/0.52  fof(f317,plain,(
% 0.21/0.52    ~r1_tarski(k3_tarski(sK0),sK0) | (spl4_3 | spl4_5 | ~spl4_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f316,f161])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    sK0 != k3_tarski(sK0) | spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f160])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    spl4_5 <=> sK0 = k3_tarski(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f316,plain,(
% 0.21/0.52    sK0 = k3_tarski(sK0) | ~r1_tarski(k3_tarski(sK0),sK0) | (spl4_3 | ~spl4_10)),
% 0.21/0.52    inference(subsumption_resolution,[],[f301,f153])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    ~r2_hidden(k3_tarski(sK0),sK0) | spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f152])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    spl4_3 <=> r2_hidden(k3_tarski(sK0),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f301,plain,(
% 0.21/0.52    r2_hidden(k3_tarski(sK0),sK0) | sK0 = k3_tarski(sK0) | ~r1_tarski(k3_tarski(sK0),sK0) | ~spl4_10),
% 0.21/0.52    inference(resolution,[],[f219,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_ordinal1(X0) | r2_hidden(X0,sK0) | sK0 = X0 | ~r1_tarski(X0,sK0)) )),
% 0.21/0.52    inference(resolution,[],[f63,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_xboole_0(X0,sK0) | r2_hidden(X0,sK0) | ~v1_ordinal1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f44,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    v3_ordinal1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ~v3_ordinal1(k3_tarski(sK0)) & v3_ordinal1(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0)) => (~v3_ordinal1(k3_tarski(sK0)) & v3_ordinal1(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f11])).
% 0.21/0.52  fof(f11,conjecture,(
% 0.21/0.52    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r2_xboole_0(X0,X1) | r2_hidden(X0,X1) | ~v1_ordinal1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).
% 0.21/0.52  fof(f219,plain,(
% 0.21/0.52    v1_ordinal1(k3_tarski(sK0)) | ~spl4_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f218])).
% 0.21/0.52  fof(f920,plain,(
% 0.21/0.52    spl4_14),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f919])).
% 0.21/0.52  fof(f919,plain,(
% 0.21/0.52    $false | spl4_14),
% 0.21/0.52    inference(subsumption_resolution,[],[f918,f785])).
% 0.21/0.52  fof(f785,plain,(
% 0.21/0.52    ~r1_tarski(sK0,sK2(sK0,sK0)) | spl4_14),
% 0.21/0.52    inference(resolution,[],[f778,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  % (28070)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.52  fof(f778,plain,(
% 0.21/0.52    r2_hidden(sK2(sK0,sK0),sK0) | spl4_14),
% 0.21/0.52    inference(resolution,[],[f253,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.21/0.52  fof(f253,plain,(
% 0.21/0.52    ~r1_tarski(k3_tarski(sK0),sK0) | spl4_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f252])).
% 0.21/0.52  fof(f918,plain,(
% 0.21/0.52    r1_tarski(sK0,sK2(sK0,sK0)) | spl4_14),
% 0.21/0.52    inference(subsumption_resolution,[],[f913,f789])).
% 0.21/0.52  fof(f789,plain,(
% 0.21/0.52    v3_ordinal1(sK2(sK0,sK0)) | spl4_14),
% 0.21/0.52    inference(subsumption_resolution,[],[f784,f42])).
% 0.21/0.52  fof(f784,plain,(
% 0.21/0.52    v3_ordinal1(sK2(sK0,sK0)) | ~v3_ordinal1(sK0) | spl4_14),
% 0.21/0.52    inference(resolution,[],[f778,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.21/0.52  fof(f913,plain,(
% 0.21/0.52    ~v3_ordinal1(sK2(sK0,sK0)) | r1_tarski(sK0,sK2(sK0,sK0)) | spl4_14),
% 0.21/0.52    inference(resolution,[],[f842,f777])).
% 0.21/0.52  fof(f777,plain,(
% 0.21/0.52    ~r1_tarski(sK2(sK0,sK0),sK0) | spl4_14),
% 0.21/0.52    inference(resolution,[],[f253,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK2(X0,X1),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f842,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(X0,sK0) | ~v3_ordinal1(X0) | r1_tarski(sK0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f414,f42])).
% 0.21/0.52  fof(f414,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X1,X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f413])).
% 0.21/0.52  fof(f413,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X1,X0) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f186,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f183])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_ordinal1(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.21/0.52    inference(resolution,[],[f51,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    ~spl4_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f235])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    $false | ~spl4_5),
% 0.21/0.52    inference(subsumption_resolution,[],[f227,f42])).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    ~v3_ordinal1(sK0) | ~spl4_5),
% 0.21/0.52    inference(backward_demodulation,[],[f43,f162])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    sK0 = k3_tarski(sK0) | ~spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f160])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ~v3_ordinal1(k3_tarski(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    ~spl4_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f172])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    $false | ~spl4_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f171,f42])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    ~v3_ordinal1(sK0) | ~spl4_3),
% 0.21/0.52    inference(subsumption_resolution,[],[f169,f43])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    v3_ordinal1(k3_tarski(sK0)) | ~v3_ordinal1(sK0) | ~spl4_3),
% 0.21/0.52    inference(resolution,[],[f154,f48])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    r2_hidden(k3_tarski(sK0),sK0) | ~spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f152])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (28049)------------------------------
% 0.21/0.52  % (28049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28049)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (28049)Memory used [KB]: 11257
% 0.21/0.52  % (28049)Time elapsed: 0.135 s
% 0.21/0.52  % (28049)------------------------------
% 0.21/0.52  % (28049)------------------------------
% 0.21/0.52  % (28075)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (28074)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (28042)Success in time 0.168 s
%------------------------------------------------------------------------------
