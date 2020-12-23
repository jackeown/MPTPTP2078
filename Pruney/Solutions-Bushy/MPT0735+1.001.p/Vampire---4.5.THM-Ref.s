%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0735+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:34 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 374 expanded)
%              Number of leaves         :   29 ( 138 expanded)
%              Depth                    :   13
%              Number of atoms          :  433 (1481 expanded)
%              Number of equality atoms :   23 (  90 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1017,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f61,f65,f103,f146,f153,f157,f196,f349,f365,f844,f853,f898,f908,f979,f1003,f1013,f1016])).

fof(f1016,plain,
    ( spl6_5
    | ~ spl6_123 ),
    inference(avatar_split_clause,[],[f1014,f1000,f92])).

fof(f92,plain,
    ( spl6_5
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f1000,plain,
    ( spl6_123
  <=> r1_tarski(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).

fof(f1014,plain,
    ( v1_ordinal1(sK0)
    | ~ spl6_123 ),
    inference(resolution,[],[f1001,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK2(X0),X0)
          & r2_hidden(sK2(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f1001,plain,
    ( r1_tarski(sK2(sK0),sK0)
    | ~ spl6_123 ),
    inference(avatar_component_clause,[],[f1000])).

fof(f1013,plain,
    ( spl6_123
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f1007,f977,f1000])).

fof(f977,plain,
    ( spl6_121
  <=> r2_hidden(sK5(sK2(sK0),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).

fof(f1007,plain,
    ( r1_tarski(sK2(sK0),sK0)
    | ~ spl6_121 ),
    inference(resolution,[],[f978,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f978,plain,
    ( r2_hidden(sK5(sK2(sK0),sK0),sK0)
    | ~ spl6_121 ),
    inference(avatar_component_clause,[],[f977])).

fof(f1003,plain,
    ( spl6_123
    | ~ spl6_7
    | ~ spl6_120 ),
    inference(avatar_split_clause,[],[f995,f973,f101,f1000])).

fof(f101,plain,
    ( spl6_7
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f973,plain,
    ( spl6_120
  <=> sK0 = sK5(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).

fof(f995,plain,
    ( ~ r2_hidden(sK2(sK0),sK0)
    | r1_tarski(sK2(sK0),sK0)
    | ~ spl6_120 ),
    inference(superposition,[],[f75,f974])).

fof(f974,plain,
    ( sK0 = sK5(sK2(sK0),sK0)
    | ~ spl6_120 ),
    inference(avatar_component_clause,[],[f973])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK5(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f51,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f979,plain,
    ( spl6_120
    | spl6_46
    | spl6_121
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f957,f363,f63,f59,f977,f347,f973])).

fof(f347,plain,
    ( spl6_46
  <=> r2_hidden(sK0,sK5(sK2(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f59,plain,
    ( spl6_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f63,plain,
    ( spl6_3
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f363,plain,
    ( spl6_49
  <=> r2_hidden(sK5(sK2(sK0),sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f957,plain,
    ( r2_hidden(sK5(sK2(sK0),sK0),sK0)
    | r2_hidden(sK0,sK5(sK2(sK0),sK0))
    | sK0 = sK5(sK2(sK0),sK0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_49 ),
    inference(resolution,[],[f364,f760])).

fof(f760,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0)
        | r2_hidden(sK0,X0)
        | sK0 = X0 )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f172,f60])).

fof(f60,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK1)
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(X1,X0)
        | X0 = X1 )
    | ~ spl6_3 ),
    inference(resolution,[],[f117,f64])).

fof(f64,plain,
    ( v3_ordinal1(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f117,plain,(
    ! [X10,X8,X9] :
      ( ~ v3_ordinal1(X10)
      | r2_hidden(X8,X9)
      | ~ r2_hidden(X9,X10)
      | ~ r2_hidden(X8,X10)
      | r2_hidden(X9,X8)
      | X8 = X9 ) ),
    inference(resolution,[],[f43,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f43,plain,(
    ! [X4,X0,X3] :
      ( ~ v2_ordinal1(X0)
      | X3 = X4
      | r2_hidden(X3,X4)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X4,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        | ( ~ r2_hidden(sK4(X0),sK3(X0))
          & sK3(X0) != sK4(X0)
          & ~ r2_hidden(sK3(X0),sK4(X0))
          & r2_hidden(sK4(X0),X0)
          & r2_hidden(sK3(X0),X0) ) )
      & ( ! [X3,X4] :
            ( r2_hidden(X4,X3)
            | X3 = X4
            | r2_hidden(X3,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) )
        | ~ v2_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X1)
          & X1 != X2
          & ~ r2_hidden(X1,X2)
          & r2_hidden(X2,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK4(X0),sK3(X0))
        & sK3(X0) != sK4(X0)
        & ~ r2_hidden(sK3(X0),sK4(X0))
        & r2_hidden(sK4(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

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

fof(f364,plain,
    ( r2_hidden(sK5(sK2(sK0),sK0),sK1)
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f363])).

fof(f908,plain,
    ( spl6_14
    | ~ spl6_98 ),
    inference(avatar_split_clause,[],[f900,f741,f148])).

fof(f148,plain,
    ( spl6_14
  <=> v2_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f741,plain,
    ( spl6_98
  <=> r2_hidden(sK3(sK0),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f900,plain,
    ( v2_ordinal1(sK0)
    | ~ spl6_98 ),
    inference(resolution,[],[f840,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK4(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f840,plain,
    ( r2_hidden(sK3(sK0),sK4(sK0))
    | ~ spl6_98 ),
    inference(avatar_component_clause,[],[f741])).

fof(f898,plain,
    ( spl6_14
    | ~ spl6_107 ),
    inference(avatar_split_clause,[],[f880,f838,f148])).

fof(f838,plain,
    ( spl6_107
  <=> sK3(sK0) = sK4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_107])])).

fof(f880,plain,
    ( v2_ordinal1(sK0)
    | ~ spl6_107 ),
    inference(trivial_inequality_removal,[],[f876])).

fof(f876,plain,
    ( sK3(sK0) != sK3(sK0)
    | v2_ordinal1(sK0)
    | ~ spl6_107 ),
    inference(superposition,[],[f47,f839])).

fof(f839,plain,
    ( sK3(sK0) = sK4(sK0)
    | ~ spl6_107 ),
    inference(avatar_component_clause,[],[f838])).

fof(f47,plain,(
    ! [X0] :
      ( sK3(X0) != sK4(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f853,plain,
    ( spl6_14
    | ~ spl6_108 ),
    inference(avatar_split_clause,[],[f845,f842,f148])).

fof(f842,plain,
    ( spl6_108
  <=> r2_hidden(sK4(sK0),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).

fof(f845,plain,
    ( v2_ordinal1(sK0)
    | ~ spl6_108 ),
    inference(resolution,[],[f843,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0),sK3(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f843,plain,
    ( r2_hidden(sK4(sK0),sK3(sK0))
    | ~ spl6_108 ),
    inference(avatar_component_clause,[],[f842])).

fof(f844,plain,
    ( spl6_107
    | spl6_98
    | spl6_108
    | ~ spl6_3
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f830,f155,f151,f63,f842,f741,f838])).

fof(f151,plain,
    ( spl6_15
  <=> r2_hidden(sK3(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f155,plain,
    ( spl6_16
  <=> r2_hidden(sK4(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f830,plain,
    ( r2_hidden(sK4(sK0),sK3(sK0))
    | r2_hidden(sK3(sK0),sK4(sK0))
    | sK3(sK0) = sK4(sK0)
    | ~ spl6_3
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(resolution,[],[f762,f156])).

fof(f156,plain,
    ( r2_hidden(sK4(sK0),sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f762,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK1)
        | r2_hidden(X4,sK3(sK0))
        | r2_hidden(sK3(sK0),X4)
        | sK3(sK0) = X4 )
    | ~ spl6_3
    | ~ spl6_15 ),
    inference(resolution,[],[f172,f152])).

fof(f152,plain,
    ( r2_hidden(sK3(sK0),sK1)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f151])).

fof(f365,plain,
    ( spl6_5
    | spl6_49
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f359,f144,f63,f363,f92])).

fof(f144,plain,
    ( spl6_13
  <=> r2_hidden(sK2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f359,plain,
    ( r2_hidden(sK5(sK2(sK0),sK0),sK1)
    | v1_ordinal1(sK0)
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(resolution,[],[f246,f42])).

fof(f246,plain,
    ( ! [X0] :
        ( r1_tarski(sK2(sK0),X0)
        | r2_hidden(sK5(sK2(sK0),X0),sK1) )
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(resolution,[],[f219,f51])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(resolution,[],[f145,f119])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,X0)
        | r2_hidden(X1,sK1) )
    | ~ spl6_3 ),
    inference(resolution,[],[f87,f64])).

fof(f87,plain,(
    ! [X4,X5,X3] :
      ( ~ v3_ordinal1(X4)
      | ~ r2_hidden(X5,X4)
      | ~ r2_hidden(X3,X5)
      | r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f78,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_ordinal1(X2)
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f50,f40])).

fof(f40,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f145,plain,
    ( r2_hidden(sK2(sK0),sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f349,plain,
    ( ~ spl6_46
    | spl6_5
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f343,f101,f92,f347])).

fof(f343,plain,
    ( ~ r2_hidden(sK0,sK5(sK2(sK0),sK0))
    | spl6_5
    | ~ spl6_7 ),
    inference(resolution,[],[f223,f102])).

fof(f102,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f223,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK2(sK0),X4)
        | ~ r2_hidden(X4,sK5(sK2(sK0),sK0)) )
    | spl6_5 ),
    inference(resolution,[],[f88,f93])).

fof(f93,plain,
    ( ~ v1_ordinal1(sK0)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_ordinal1(X0)
      | ~ r2_hidden(X1,sK5(sK2(X0),X0))
      | ~ r2_hidden(sK2(X0),X1) ) ),
    inference(resolution,[],[f83,f42])).

fof(f83,plain,(
    ! [X6,X7,X5] :
      ( r1_tarski(X6,X7)
      | ~ r2_hidden(X6,X5)
      | ~ r2_hidden(X5,sK5(X6,X7)) ) ),
    inference(resolution,[],[f53,f51])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X2,X0)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_ordinal1)).

fof(f196,plain,
    ( ~ spl6_5
    | spl6_1
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f165,f148,f55,f92])).

fof(f55,plain,
    ( spl6_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f165,plain,
    ( v3_ordinal1(sK0)
    | ~ v1_ordinal1(sK0)
    | ~ spl6_14 ),
    inference(resolution,[],[f149,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v2_ordinal1(X0)
      | v3_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f149,plain,
    ( v2_ordinal1(sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f157,plain,
    ( spl6_14
    | spl6_16
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f141,f63,f59,f155,f148])).

fof(f141,plain,
    ( r2_hidden(sK4(sK0),sK1)
    | v2_ordinal1(sK0)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f122,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,sK1) )
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f119,f60])).

fof(f153,plain,
    ( spl6_14
    | spl6_15
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f140,f63,f59,f151,f148])).

fof(f140,plain,
    ( r2_hidden(sK3(sK0),sK1)
    | v2_ordinal1(sK0)
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f122,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f146,plain,
    ( spl6_13
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f139,f101,f63,f59,f144])).

fof(f139,plain,
    ( r2_hidden(sK2(sK0),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_7 ),
    inference(resolution,[],[f122,f102])).

fof(f103,plain,
    ( spl6_7
    | spl6_5 ),
    inference(avatar_split_clause,[],[f98,f92,f101])).

fof(f98,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | spl6_5 ),
    inference(resolution,[],[f93,f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f34,f63])).

fof(f34,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ v3_ordinal1(sK0)
    & r2_hidden(sK0,sK1)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ~ v3_ordinal1(X0)
        & r2_hidden(X0,X1)
        & v3_ordinal1(X1) )
   => ( ~ v3_ordinal1(sK0)
      & r2_hidden(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ v3_ordinal1(X0)
      & r2_hidden(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ v3_ordinal1(X0)
      & r2_hidden(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ( r2_hidden(X0,X1)
         => v3_ordinal1(X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f61,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f35,f59])).

fof(f35,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f36,f55])).

fof(f36,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
