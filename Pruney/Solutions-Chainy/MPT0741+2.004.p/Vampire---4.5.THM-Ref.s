%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 172 expanded)
%              Number of leaves         :   19 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  281 ( 627 expanded)
%              Number of equality atoms :   16 (  40 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f61,f67,f71,f75,f89,f120,f130,f169])).

fof(f169,plain,
    ( ~ spl4_2
    | ~ spl4_8
    | ~ spl4_17
    | spl4_1 ),
    inference(avatar_split_clause,[],[f166,f49,f128,f87,f56])).

fof(f56,plain,
    ( spl4_2
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f87,plain,
    ( spl4_8
  <=> v3_ordinal1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f128,plain,
    ( spl4_17
  <=> v3_ordinal1(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f49,plain,
    ( spl4_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f166,plain,
    ( ~ v3_ordinal1(sK3(sK0))
    | ~ v3_ordinal1(sK2(sK0))
    | ~ v1_ordinal1(sK0)
    | spl4_1 ),
    inference(resolution,[],[f165,f50])).

fof(f50,plain,
    ( ~ v3_ordinal1(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f165,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v3_ordinal1(sK3(X0))
      | ~ v3_ordinal1(sK2(X0))
      | ~ v1_ordinal1(X0) ) ),
    inference(resolution,[],[f164,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_ordinal1(X0)
      | v3_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_ordinal1)).

fof(f164,plain,(
    ! [X2] :
      ( v2_ordinal1(X2)
      | ~ v3_ordinal1(sK2(X2))
      | ~ v3_ordinal1(sK3(X2)) ) ),
    inference(global_subsumption,[],[f43,f42,f160])).

fof(f160,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(sK3(X2))
      | sK3(X2) = sK2(X2)
      | ~ v3_ordinal1(sK2(X2))
      | r2_hidden(sK3(X2),sK2(X2))
      | v2_ordinal1(X2) ) ),
    inference(resolution,[],[f157,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0),sK3(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ( ~ r2_hidden(sK3(X0),sK2(X0))
        & sK2(X0) != sK3(X0)
        & ~ r2_hidden(sK2(X0),sK3(X0))
        & r2_hidden(sK3(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK3(X0),sK2(X0))
        & sK2(X0) != sK3(X0)
        & ~ r2_hidden(sK2(X0),sK3(X0))
        & r2_hidden(sK3(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) )
     => v2_ordinal1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).

fof(f157,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | X0 = X1
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0)
      | X0 = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f149,f150])).

fof(f150,plain,(
    ! [X2,X3] :
      ( ~ r2_xboole_0(X2,X3)
      | ~ v3_ordinal1(X3)
      | r2_hidden(X2,X3)
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f146,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f146,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f44,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f149,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X1,X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f146,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f42,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK2(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f130,plain,
    ( spl4_17
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f122,f118,f128])).

fof(f118,plain,
    ( spl4_15
  <=> r2_hidden(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f122,plain,
    ( v3_ordinal1(sK3(sK0))
    | ~ spl4_15 ),
    inference(resolution,[],[f119,f32])).

fof(f32,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v3_ordinal1(sK0)
    & ! [X1] :
        ( ( r1_tarski(X1,sK0)
          & v3_ordinal1(X1) )
        | ~ r2_hidden(X1,sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ~ v3_ordinal1(X0)
        & ! [X1] :
            ( ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) )
            | ~ r2_hidden(X1,X0) ) )
   => ( ~ v3_ordinal1(sK0)
      & ! [X1] :
          ( ( r1_tarski(X1,sK0)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(X0)
      & ! [X1] :
          ( ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) ) )
       => v3_ordinal1(X0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) ) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_ordinal1)).

fof(f119,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,
    ( ~ spl4_2
    | spl4_15
    | spl4_1 ),
    inference(avatar_split_clause,[],[f116,f49,f118,f56])).

fof(f116,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ v1_ordinal1(sK0)
    | spl4_1 ),
    inference(resolution,[],[f53,f50])).

fof(f53,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | r2_hidden(sK3(X0),X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(resolution,[],[f40,f36])).

fof(f40,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,
    ( spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f81,f59,f87])).

fof(f59,plain,
    ( spl4_3
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f81,plain,
    ( v3_ordinal1(sK2(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f60,f32])).

fof(f60,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f75,plain,
    ( spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f72,f69,f65])).

fof(f65,plain,
    ( spl4_4
  <=> r1_tarski(sK1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f69,plain,
    ( spl4_5
  <=> r2_hidden(sK1(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f72,plain,
    ( r1_tarski(sK1(sK0),sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f70,f33])).

fof(f33,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r1_tarski(X1,sK0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,
    ( r2_hidden(sK1(sK0),sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,
    ( spl4_5
    | spl4_2 ),
    inference(avatar_split_clause,[],[f63,f56,f69])).

fof(f63,plain,
    ( r2_hidden(sK1(sK0),sK0)
    | spl4_2 ),
    inference(resolution,[],[f57,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ( ~ r1_tarski(sK1(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK1(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) )
     => v1_ordinal1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f57,plain,
    ( ~ v1_ordinal1(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f67,plain,
    ( ~ spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f62,f56,f65])).

fof(f62,plain,
    ( ~ r1_tarski(sK1(sK0),sK0)
    | spl4_2 ),
    inference(resolution,[],[f57,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,
    ( ~ spl4_2
    | spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f54,f49,f59,f56])).

fof(f54,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ v1_ordinal1(sK0)
    | spl4_1 ),
    inference(resolution,[],[f52,f50])).

fof(f52,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | r2_hidden(sK2(X0),X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(resolution,[],[f39,f36])).

fof(f39,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f34,f49])).

fof(f34,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.40  % (1626)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (1633)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (1633)Refutation not found, incomplete strategy% (1633)------------------------------
% 0.21/0.47  % (1633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (1633)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (1633)Memory used [KB]: 10618
% 0.21/0.47  % (1633)Time elapsed: 0.007 s
% 0.21/0.47  % (1633)------------------------------
% 0.21/0.47  % (1633)------------------------------
% 0.21/0.47  % (1625)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (1625)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f170,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f51,f61,f67,f71,f75,f89,f120,f130,f169])).
% 0.21/0.47  fof(f169,plain,(
% 0.21/0.47    ~spl4_2 | ~spl4_8 | ~spl4_17 | spl4_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f166,f49,f128,f87,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl4_2 <=> v1_ordinal1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    spl4_8 <=> v3_ordinal1(sK2(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    spl4_17 <=> v3_ordinal1(sK3(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl4_1 <=> v3_ordinal1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    ~v3_ordinal1(sK3(sK0)) | ~v3_ordinal1(sK2(sK0)) | ~v1_ordinal1(sK0) | spl4_1),
% 0.21/0.47    inference(resolution,[],[f165,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ~v3_ordinal1(sK0) | spl4_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f49])).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    ( ! [X0] : (v3_ordinal1(X0) | ~v3_ordinal1(sK3(X0)) | ~v3_ordinal1(sK2(X0)) | ~v1_ordinal1(X0)) )),
% 0.21/0.47    inference(resolution,[],[f164,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_ordinal1(X0) | v3_ordinal1(X0) | ~v1_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (v3_ordinal1(X0) | ~v2_ordinal1(X0) | ~v1_ordinal1(X0))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (v3_ordinal1(X0) | (~v2_ordinal1(X0) | ~v1_ordinal1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) => v3_ordinal1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_ordinal1)).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    ( ! [X2] : (v2_ordinal1(X2) | ~v3_ordinal1(sK2(X2)) | ~v3_ordinal1(sK3(X2))) )),
% 0.21/0.47    inference(global_subsumption,[],[f43,f42,f160])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    ( ! [X2] : (~v3_ordinal1(sK3(X2)) | sK3(X2) = sK2(X2) | ~v3_ordinal1(sK2(X2)) | r2_hidden(sK3(X2),sK2(X2)) | v2_ordinal1(X2)) )),
% 0.21/0.47    inference(resolution,[],[f157,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK2(X0),sK3(X0)) | v2_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0] : (v2_ordinal1(X0) | (~r2_hidden(sK3(X0),sK2(X0)) & sK2(X0) != sK3(X0) & ~r2_hidden(sK2(X0),sK3(X0)) & r2_hidden(sK3(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0] : (? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) => (~r2_hidden(sK3(X0),sK2(X0)) & sK2(X0) != sK3(X0) & ~r2_hidden(sK2(X0),sK3(X0)) & r2_hidden(sK3(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (v2_ordinal1(X0) | ? [X1,X2] : (~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ~(~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)) => v2_ordinal1(X0))),
% 0.21/0.47    inference(unused_predicate_definition_removal,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (v2_ordinal1(X0) <=> ! [X1,X2] : ~(~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~v3_ordinal1(X0) | X0 = X1 | ~v3_ordinal1(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f156])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v3_ordinal1(X0) | r2_hidden(X1,X0) | X0 = X1 | ~v3_ordinal1(X1) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.47    inference(resolution,[],[f149,f150])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    ( ! [X2,X3] : (~r2_xboole_0(X2,X3) | ~v3_ordinal1(X3) | r2_hidden(X2,X3) | ~v3_ordinal1(X2)) )),
% 0.21/0.47    inference(resolution,[],[f146,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f145])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.47    inference(resolution,[],[f44,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_xboole_0(X1,X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | ~v3_ordinal1(X0)) )),
% 0.21/0.47    inference(resolution,[],[f146,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.21/0.47    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0] : (sK2(X0) != sK3(X0) | v2_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK3(X0),sK2(X0)) | v2_ordinal1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    spl4_17 | ~spl4_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f122,f118,f128])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    spl4_15 <=> r2_hidden(sK3(sK0),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    v3_ordinal1(sK3(sK0)) | ~spl4_15),
% 0.21/0.47    inference(resolution,[],[f119,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_hidden(X1,sK0) | v3_ordinal1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ~v3_ordinal1(sK0) & ! [X1] : ((r1_tarski(X1,sK0) & v3_ordinal1(X1)) | ~r2_hidden(X1,sK0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ? [X0] : (~v3_ordinal1(X0) & ! [X1] : ((r1_tarski(X1,X0) & v3_ordinal1(X1)) | ~r2_hidden(X1,X0))) => (~v3_ordinal1(sK0) & ! [X1] : ((r1_tarski(X1,sK0) & v3_ordinal1(X1)) | ~r2_hidden(X1,sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0] : (~v3_ordinal1(X0) & ! [X1] : ((r1_tarski(X1,X0) & v3_ordinal1(X1)) | ~r2_hidden(X1,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 0.21/0.47    inference(negated_conjecture,[],[f8])).
% 0.21/0.47  fof(f8,conjecture,(
% 0.21/0.47    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_ordinal1)).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    r2_hidden(sK3(sK0),sK0) | ~spl4_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f118])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ~spl4_2 | spl4_15 | spl4_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f116,f49,f118,f56])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    r2_hidden(sK3(sK0),sK0) | ~v1_ordinal1(sK0) | spl4_1),
% 0.21/0.47    inference(resolution,[],[f53,f50])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0] : (v3_ordinal1(X0) | r2_hidden(sK3(X0),X0) | ~v1_ordinal1(X0)) )),
% 0.21/0.47    inference(resolution,[],[f40,f36])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0] : (v2_ordinal1(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl4_8 | ~spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f81,f59,f87])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl4_3 <=> r2_hidden(sK2(sK0),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    v3_ordinal1(sK2(sK0)) | ~spl4_3),
% 0.21/0.47    inference(resolution,[],[f60,f32])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    r2_hidden(sK2(sK0),sK0) | ~spl4_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    spl4_4 | ~spl4_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f72,f69,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl4_4 <=> r1_tarski(sK1(sK0),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl4_5 <=> r2_hidden(sK1(sK0),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    r1_tarski(sK1(sK0),sK0) | ~spl4_5),
% 0.21/0.47    inference(resolution,[],[f70,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X1] : (~r2_hidden(X1,sK0) | r1_tarski(X1,sK0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    r2_hidden(sK1(sK0),sK0) | ~spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl4_5 | spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f63,f56,f69])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    r2_hidden(sK1(sK0),sK0) | spl4_2),
% 0.21/0.48    inference(resolution,[],[f57,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (v1_ordinal1(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (v1_ordinal1(X0) | (~r1_tarski(sK1(X0),X0) & r2_hidden(sK1(X0),X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK1(X0),X0) & r2_hidden(sK1(X0),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)) => v1_ordinal1(X0))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ~v1_ordinal1(sK0) | spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~spl4_4 | spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f62,f56,f65])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ~r1_tarski(sK1(sK0),sK0) | spl4_2),
% 0.21/0.48    inference(resolution,[],[f57,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (v1_ordinal1(X0) | ~r1_tarski(sK1(X0),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ~spl4_2 | spl4_3 | spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f54,f49,f59,f56])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0),sK0) | ~v1_ordinal1(sK0) | spl4_1),
% 0.21/0.48    inference(resolution,[],[f52,f50])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0] : (v3_ordinal1(X0) | r2_hidden(sK2(X0),X0) | ~v1_ordinal1(X0)) )),
% 0.21/0.48    inference(resolution,[],[f39,f36])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (v2_ordinal1(X0) | r2_hidden(sK2(X0),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ~spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f49])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ~v3_ordinal1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (1625)------------------------------
% 0.21/0.48  % (1625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (1625)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (1625)Memory used [KB]: 10618
% 0.21/0.48  % (1625)Time elapsed: 0.008 s
% 0.21/0.48  % (1625)------------------------------
% 0.21/0.48  % (1625)------------------------------
% 0.21/0.48  % (1618)Success in time 0.125 s
%------------------------------------------------------------------------------
