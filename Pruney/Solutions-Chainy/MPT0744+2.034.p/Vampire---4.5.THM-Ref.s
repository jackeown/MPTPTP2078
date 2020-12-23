%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 160 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :    9
%              Number of atoms          :  292 ( 540 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f312,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f92,f93,f100,f140,f163,f173,f178,f187,f188,f283,f303,f311])).

fof(f311,plain,
    ( ~ spl3_2
    | spl3_23 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl3_2
    | spl3_23 ),
    inference(unit_resulting_resolution,[],[f82,f302,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f60,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f52,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f302,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl3_23
  <=> v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f82,plain,
    ( v3_ordinal1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_2
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f303,plain,
    ( spl3_3
    | ~ spl3_23
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f286,f281,f300,f85])).

fof(f85,plain,
    ( spl3_3
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f281,plain,
    ( spl3_20
  <=> ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ v3_ordinal1(X0)
        | r2_hidden(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f286,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))
    | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl3_20 ),
    inference(resolution,[],[f282,f68])).

fof(f68,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f51,f60])).

fof(f51,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f282,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ v3_ordinal1(X0)
        | r2_hidden(sK0,X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f281])).

fof(f283,plain,
    ( ~ spl3_5
    | ~ spl3_2
    | spl3_20
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f190,f160,f281,f80,f97])).

fof(f97,plain,
    ( spl3_5
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f160,plain,
    ( spl3_12
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | r2_hidden(sK0,X0)
        | ~ v3_ordinal1(X0)
        | ~ v3_ordinal1(sK1)
        | ~ v1_ordinal1(sK0) )
    | ~ spl3_12 ),
    inference(resolution,[],[f162,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

fof(f162,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f160])).

fof(f188,plain,
    ( sK0 != sK1
    | r1_ordinal1(sK0,sK1)
    | ~ r1_ordinal1(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f187,plain,
    ( spl3_14
    | spl3_11
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f166,f85,f147,f184])).

fof(f184,plain,
    ( spl3_14
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f147,plain,
    ( spl3_11
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f166,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | ~ spl3_3 ),
    inference(resolution,[],[f86,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f47,f60])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f86,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f178,plain,
    ( ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f149,f172,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f172,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl3_13
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f149,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f147])).

fof(f173,plain,
    ( ~ spl3_2
    | ~ spl3_1
    | spl3_13
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f141,f137,f170,f75,f80])).

fof(f75,plain,
    ( spl3_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f137,plain,
    ( spl3_9
  <=> r1_ordinal1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f141,plain,
    ( r1_tarski(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl3_9 ),
    inference(resolution,[],[f139,f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f139,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f137])).

fof(f163,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_12
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f151,f89,f160,f80,f75])).

fof(f89,plain,
    ( spl3_4
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f151,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f90,f43])).

fof(f90,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f140,plain,
    ( ~ spl3_2
    | ~ spl3_1
    | spl3_9
    | spl3_4 ),
    inference(avatar_split_clause,[],[f127,f89,f137,f75,f80])).

fof(f127,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | spl3_4 ),
    inference(resolution,[],[f45,f91])).

fof(f91,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

% (24757)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f17,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f100,plain,
    ( spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f94,f75,f97])).

fof(f94,plain,
    ( v1_ordinal1(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f61,f77])).

fof(f77,plain,
    ( v3_ordinal1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f93,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f64,f89,f85])).

fof(f64,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f41,f60])).

fof(f41,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_ordinal1(sK0,sK1)
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( r1_ordinal1(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK0,X1)
            | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK0,X1)
            | r2_hidden(sK0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

% (24746)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (24749)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (24768)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f29,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK0,X1)
          | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK0,X1)
          | r2_hidden(sK0,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK0,sK1)
        | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
      & ( r1_ordinal1(sK0,sK1)
        | r2_hidden(sK0,k1_ordinal1(sK1)) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f92,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f63,f89,f85])).

fof(f63,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f42,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f40,f80])).

fof(f40,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f39,f75])).

fof(f39,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:49:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (24747)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (24763)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (24755)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (24763)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (24740)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.58  % (24742)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.58  % (24754)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.58  % (24762)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f312,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f78,f83,f92,f93,f100,f140,f163,f173,f178,f187,f188,f283,f303,f311])).
% 0.22/0.58  fof(f311,plain,(
% 0.22/0.58    ~spl3_2 | spl3_23),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f309])).
% 0.22/0.58  fof(f309,plain,(
% 0.22/0.58    $false | (~spl3_2 | spl3_23)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f82,f302,f69])).
% 0.22/0.58  fof(f69,plain,(
% 0.22/0.58    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 0.22/0.58    inference(definition_unfolding,[],[f52,f60])).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f4])).
% 0.22/0.58  fof(f4,axiom,(
% 0.22/0.58    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f10])).
% 0.22/0.58  fof(f10,axiom,(
% 0.22/0.58    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.22/0.58  fof(f302,plain,(
% 0.22/0.58    ~v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | spl3_23),
% 0.22/0.58    inference(avatar_component_clause,[],[f300])).
% 0.22/0.58  fof(f300,plain,(
% 0.22/0.58    spl3_23 <=> v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.58  fof(f82,plain,(
% 0.22/0.58    v3_ordinal1(sK1) | ~spl3_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f80])).
% 0.22/0.58  fof(f80,plain,(
% 0.22/0.58    spl3_2 <=> v3_ordinal1(sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.58  fof(f303,plain,(
% 0.22/0.58    spl3_3 | ~spl3_23 | ~spl3_20),
% 0.22/0.58    inference(avatar_split_clause,[],[f286,f281,f300,f85])).
% 0.22/0.58  fof(f85,plain,(
% 0.22/0.58    spl3_3 <=> r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.58  fof(f281,plain,(
% 0.22/0.58    spl3_20 <=> ! [X0] : (~r2_hidden(sK1,X0) | ~v3_ordinal1(X0) | r2_hidden(sK0,X0))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.58  fof(f286,plain,(
% 0.22/0.58    ~v3_ordinal1(k2_xboole_0(sK1,k1_tarski(sK1))) | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl3_20),
% 0.22/0.58    inference(resolution,[],[f282,f68])).
% 0.22/0.58  fof(f68,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 0.22/0.58    inference(definition_unfolding,[],[f51,f60])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.22/0.58  fof(f282,plain,(
% 0.22/0.58    ( ! [X0] : (~r2_hidden(sK1,X0) | ~v3_ordinal1(X0) | r2_hidden(sK0,X0)) ) | ~spl3_20),
% 0.22/0.58    inference(avatar_component_clause,[],[f281])).
% 0.22/0.58  fof(f283,plain,(
% 0.22/0.58    ~spl3_5 | ~spl3_2 | spl3_20 | ~spl3_12),
% 0.22/0.58    inference(avatar_split_clause,[],[f190,f160,f281,f80,f97])).
% 0.22/0.58  fof(f97,plain,(
% 0.22/0.58    spl3_5 <=> v1_ordinal1(sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.58  fof(f160,plain,(
% 0.22/0.58    spl3_12 <=> r1_tarski(sK0,sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.58  fof(f190,plain,(
% 0.22/0.58    ( ! [X0] : (~r2_hidden(sK1,X0) | r2_hidden(sK0,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(sK1) | ~v1_ordinal1(sK0)) ) | ~spl3_12),
% 0.22/0.58    inference(resolution,[],[f162,f53])).
% 0.22/0.58  fof(f53,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2) | ~v3_ordinal1(X2) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X2)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.22/0.58    inference(flattening,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X0,X2) | (~r2_hidden(X1,X2) | ~r1_tarski(X0,X1))) | ~v3_ordinal1(X2)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ! [X2] : (v3_ordinal1(X2) => ((r2_hidden(X1,X2) & r1_tarski(X0,X1)) => r2_hidden(X0,X2)))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).
% 0.22/0.58  fof(f162,plain,(
% 0.22/0.58    r1_tarski(sK0,sK1) | ~spl3_12),
% 0.22/0.58    inference(avatar_component_clause,[],[f160])).
% 0.22/0.58  fof(f188,plain,(
% 0.22/0.58    sK0 != sK1 | r1_ordinal1(sK0,sK1) | ~r1_ordinal1(sK1,sK0)),
% 0.22/0.58    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.58  fof(f187,plain,(
% 0.22/0.58    spl3_14 | spl3_11 | ~spl3_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f166,f85,f147,f184])).
% 0.22/0.58  fof(f184,plain,(
% 0.22/0.58    spl3_14 <=> sK0 = sK1),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.58  fof(f147,plain,(
% 0.22/0.58    spl3_11 <=> r2_hidden(sK0,sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.58  fof(f166,plain,(
% 0.22/0.58    r2_hidden(sK0,sK1) | sK0 = sK1 | ~spl3_3),
% 0.22/0.58    inference(resolution,[],[f86,f67])).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.22/0.58    inference(definition_unfolding,[],[f47,f60])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.22/0.58    inference(flattening,[],[f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.22/0.58    inference(nnf_transformation,[],[f7])).
% 0.22/0.58  fof(f7,axiom,(
% 0.22/0.58    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.22/0.58  fof(f86,plain,(
% 0.22/0.58    r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1))) | ~spl3_3),
% 0.22/0.58    inference(avatar_component_clause,[],[f85])).
% 0.22/0.58  fof(f178,plain,(
% 0.22/0.58    ~spl3_11 | ~spl3_13),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f174])).
% 0.22/0.58  fof(f174,plain,(
% 0.22/0.58    $false | (~spl3_11 | ~spl3_13)),
% 0.22/0.58    inference(unit_resulting_resolution,[],[f149,f172,f46])).
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,axiom,(
% 0.22/0.58    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.58  fof(f172,plain,(
% 0.22/0.58    r1_tarski(sK1,sK0) | ~spl3_13),
% 0.22/0.58    inference(avatar_component_clause,[],[f170])).
% 0.22/0.58  fof(f170,plain,(
% 0.22/0.58    spl3_13 <=> r1_tarski(sK1,sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.58  fof(f149,plain,(
% 0.22/0.58    r2_hidden(sK0,sK1) | ~spl3_11),
% 0.22/0.58    inference(avatar_component_clause,[],[f147])).
% 0.22/0.58  fof(f173,plain,(
% 0.22/0.58    ~spl3_2 | ~spl3_1 | spl3_13 | ~spl3_9),
% 0.22/0.58    inference(avatar_split_clause,[],[f141,f137,f170,f75,f80])).
% 0.22/0.58  fof(f75,plain,(
% 0.22/0.58    spl3_1 <=> v3_ordinal1(sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.58  fof(f137,plain,(
% 0.22/0.58    spl3_9 <=> r1_ordinal1(sK1,sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.58  fof(f141,plain,(
% 0.22/0.58    r1_tarski(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | ~spl3_9),
% 0.22/0.58    inference(resolution,[],[f139,f43])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.58    inference(nnf_transformation,[],[f16])).
% 0.22/0.58  fof(f16,plain,(
% 0.22/0.58    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.58    inference(flattening,[],[f15])).
% 0.22/0.58  fof(f15,plain,(
% 0.22/0.58    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.58  fof(f139,plain,(
% 0.22/0.58    r1_ordinal1(sK1,sK0) | ~spl3_9),
% 0.22/0.58    inference(avatar_component_clause,[],[f137])).
% 0.22/0.58  fof(f163,plain,(
% 0.22/0.58    ~spl3_1 | ~spl3_2 | spl3_12 | ~spl3_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f151,f89,f160,f80,f75])).
% 0.22/0.58  fof(f89,plain,(
% 0.22/0.58    spl3_4 <=> r1_ordinal1(sK0,sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.58  fof(f151,plain,(
% 0.22/0.58    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~spl3_4),
% 0.22/0.58    inference(resolution,[],[f90,f43])).
% 0.22/0.58  fof(f90,plain,(
% 0.22/0.58    r1_ordinal1(sK0,sK1) | ~spl3_4),
% 0.22/0.58    inference(avatar_component_clause,[],[f89])).
% 0.22/0.58  fof(f140,plain,(
% 0.22/0.58    ~spl3_2 | ~spl3_1 | spl3_9 | spl3_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f127,f89,f137,f75,f80])).
% 0.22/0.58  fof(f127,plain,(
% 0.22/0.58    r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | spl3_4),
% 0.22/0.58    inference(resolution,[],[f45,f91])).
% 0.22/0.58  fof(f91,plain,(
% 0.22/0.58    ~r1_ordinal1(sK0,sK1) | spl3_4),
% 0.22/0.58    inference(avatar_component_clause,[],[f89])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f18])).
% 0.22/0.58  fof(f18,plain,(
% 0.22/0.58    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.58    inference(flattening,[],[f17])).
% 0.22/0.58  % (24757)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.58  fof(f17,plain,(
% 0.22/0.58    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.22/0.58  fof(f100,plain,(
% 0.22/0.58    spl3_5 | ~spl3_1),
% 0.22/0.58    inference(avatar_split_clause,[],[f94,f75,f97])).
% 0.22/0.58  fof(f94,plain,(
% 0.22/0.58    v1_ordinal1(sK0) | ~spl3_1),
% 0.22/0.58    inference(resolution,[],[f61,f77])).
% 0.22/0.58  fof(f77,plain,(
% 0.22/0.58    v3_ordinal1(sK0) | ~spl3_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f75])).
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f25])).
% 0.22/0.58  fof(f25,plain,(
% 0.22/0.58    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.22/0.58  fof(f93,plain,(
% 0.22/0.58    spl3_3 | spl3_4),
% 0.22/0.58    inference(avatar_split_clause,[],[f64,f89,f85])).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.22/0.58    inference(definition_unfolding,[],[f41,f60])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.22/0.58    inference(cnf_transformation,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).
% 0.22/0.58  fof(f28,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.59  % (24746)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.59  % (24749)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.59  % (24768)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    ? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 0.22/0.59    introduced(choice_axiom,[])).
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.59    inference(flattening,[],[f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.59    inference(nnf_transformation,[],[f14])).
% 0.22/0.59  fof(f14,plain,(
% 0.22/0.59    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.59    inference(ennf_transformation,[],[f13])).
% 0.22/0.59  fof(f13,negated_conjecture,(
% 0.22/0.59    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.22/0.59    inference(negated_conjecture,[],[f12])).
% 0.22/0.59  fof(f12,conjecture,(
% 0.22/0.59    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.22/0.59  fof(f92,plain,(
% 0.22/0.59    ~spl3_3 | ~spl3_4),
% 0.22/0.59    inference(avatar_split_clause,[],[f63,f89,f85])).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k1_tarski(sK1)))),
% 0.22/0.59    inference(definition_unfolding,[],[f42,f60])).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.22/0.59    inference(cnf_transformation,[],[f30])).
% 0.22/0.59  fof(f83,plain,(
% 0.22/0.59    spl3_2),
% 0.22/0.59    inference(avatar_split_clause,[],[f40,f80])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    v3_ordinal1(sK1)),
% 0.22/0.59    inference(cnf_transformation,[],[f30])).
% 0.22/0.59  fof(f78,plain,(
% 0.22/0.59    spl3_1),
% 0.22/0.59    inference(avatar_split_clause,[],[f39,f75])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    v3_ordinal1(sK0)),
% 0.22/0.59    inference(cnf_transformation,[],[f30])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (24763)------------------------------
% 0.22/0.59  % (24763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (24763)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (24763)Memory used [KB]: 10874
% 0.22/0.59  % (24763)Time elapsed: 0.137 s
% 0.22/0.59  % (24763)------------------------------
% 0.22/0.59  % (24763)------------------------------
% 1.55/0.59  % (24768)Refutation not found, incomplete strategy% (24768)------------------------------
% 1.55/0.59  % (24768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (24768)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.59  
% 1.55/0.59  % (24768)Memory used [KB]: 10746
% 1.55/0.59  % (24768)Time elapsed: 0.175 s
% 1.55/0.59  % (24768)------------------------------
% 1.55/0.59  % (24768)------------------------------
% 1.55/0.59  % (24739)Success in time 0.229 s
%------------------------------------------------------------------------------
