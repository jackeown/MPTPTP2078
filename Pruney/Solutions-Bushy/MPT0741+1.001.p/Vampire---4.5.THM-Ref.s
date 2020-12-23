%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0741+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:34 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 143 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  229 ( 703 expanded)
%              Number of equality atoms :   16 (  56 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f61,f65,f99])).

fof(f99,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f97,f42])).

fof(f42,plain,(
    v1_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f40,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK1(X0),X0)
          & r2_hidden(sK1(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK1(X0),X0)
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f40,plain,
    ( v1_ordinal1(sK0)
    | r1_tarski(sK1(sK0),sK0) ),
    inference(resolution,[],[f29,f25])).

fof(f25,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | r1_tarski(X1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ v3_ordinal1(sK0)
    & ! [X1] :
        ( ( r1_tarski(X1,sK0)
          & v3_ordinal1(X1) )
        | ~ r2_hidden(X1,sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f12])).

fof(f12,plain,
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

fof(f7,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(X0)
      & ! [X1] :
          ( ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) )
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r1_tarski(X1,X0)
              & v3_ordinal1(X1) ) )
       => v3_ordinal1(X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) ) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_ordinal1)).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f97,plain,
    ( ~ v1_ordinal1(sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f96,f26])).

fof(f26,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f96,plain,
    ( v3_ordinal1(sK0)
    | ~ v1_ordinal1(sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f95,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v2_ordinal1(X0)
      | v3_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v3_ordinal1(X0)
        | ~ v2_ordinal1(X0)
        | ~ v1_ordinal1(X0) )
      & ( ( v2_ordinal1(X0)
          & v1_ordinal1(X0) )
        | ~ v3_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
    <=> ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_ordinal1)).

fof(f95,plain,
    ( v2_ordinal1(sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f94,f54])).

fof(f54,plain,
    ( v3_ordinal1(sK2(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_3
  <=> v3_ordinal1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f94,plain,
    ( ~ v3_ordinal1(sK2(sK0))
    | v2_ordinal1(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f86,f64])).

fof(f64,plain,
    ( v3_ordinal1(sK3(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_4
  <=> v3_ordinal1(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f86,plain,(
    ! [X4] :
      ( ~ v3_ordinal1(sK3(X4))
      | ~ v3_ordinal1(sK2(X4))
      | v2_ordinal1(X4) ) ),
    inference(subsumption_resolution,[],[f85,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK2(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ( ~ r2_hidden(sK3(X0),sK2(X0))
          & sK2(X0) != sK3(X0)
          & ~ r2_hidden(sK2(X0),sK3(X0))
          & r2_hidden(sK3(X0),X0)
          & r2_hidden(sK2(X0),X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f19,f20])).

fof(f20,plain,(
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
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ? [X1,X2] :
            ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1,X2] :
            ( r2_hidden(X2,X1)
            | X1 = X2
            | r2_hidden(X1,X2)
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).

fof(f85,plain,(
    ! [X4] :
      ( r2_hidden(sK3(X4),sK2(X4))
      | ~ v3_ordinal1(sK2(X4))
      | ~ v3_ordinal1(sK3(X4))
      | v2_ordinal1(X4) ) ),
    inference(subsumption_resolution,[],[f80,f35])).

fof(f35,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    ! [X4] :
      ( sK3(X4) = sK2(X4)
      | r2_hidden(sK3(X4),sK2(X4))
      | ~ v3_ordinal1(sK2(X4))
      | ~ v3_ordinal1(sK3(X4))
      | v2_ordinal1(X4) ) ),
    inference(resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0),sK3(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f65,plain,
    ( spl4_4
    | spl4_2 ),
    inference(avatar_split_clause,[],[f57,f49,f63])).

fof(f49,plain,
    ( spl4_2
  <=> v2_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f57,plain,
    ( v2_ordinal1(sK0)
    | v3_ordinal1(sK3(sK0)) ),
    inference(resolution,[],[f33,f24])).

fof(f24,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f60])).

fof(f60,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f59,f42])).

fof(f59,plain,
    ( ~ v1_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f58,f26])).

fof(f58,plain,
    ( v3_ordinal1(sK0)
    | ~ v1_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f39,f50])).

fof(f50,plain,
    ( v2_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f55,plain,
    ( spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f44,f49,f53])).

fof(f44,plain,
    ( v2_ordinal1(sK0)
    | v3_ordinal1(sK2(sK0)) ),
    inference(resolution,[],[f32,f24])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
