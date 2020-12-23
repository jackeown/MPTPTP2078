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
% DateTime   : Thu Dec  3 13:09:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 256 expanded)
%              Number of leaves         :   22 (  94 expanded)
%              Depth                    :   16
%              Number of atoms          :  432 (1531 expanded)
%              Number of equality atoms :   30 ( 196 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f122,f173,f181,f191])).

fof(f191,plain,
    ( ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f189,f42])).

fof(f42,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK3 != sK4
    & r1_orders_2(sK2,sK4,sK3)
    & r1_orders_2(sK2,sK3,sK4)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & r1_orders_2(X0,X2,X1)
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(sK2,X2,X1)
              & r1_orders_2(sK2,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & r1_orders_2(sK2,X2,X1)
            & r1_orders_2(sK2,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( sK3 != X2
          & r1_orders_2(sK2,X2,sK3)
          & r1_orders_2(sK2,sK3,X2)
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( sK3 != X2
        & r1_orders_2(sK2,X2,sK3)
        & r1_orders_2(sK2,sK3,X2)
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( sK3 != sK4
      & r1_orders_2(sK2,sK4,sK3)
      & r1_orders_2(sK2,sK3,sK4)
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X2,X1)
                    & r1_orders_2(X0,X1,X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(f189,plain,
    ( ~ l1_orders_2(sK2)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f188,f41])).

fof(f41,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f188,plain,
    ( ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f187,f88])).

fof(f88,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl8_3
  <=> r2_hidden(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f187,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f184,f79])).

fof(f79,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl8_1
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f184,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,u1_struct_0(sK2))
    | ~ v5_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | ~ spl8_5 ),
    inference(resolution,[],[f166,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v5_orders_2(X0)
          | ~ r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v5_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r4_relat_2(u1_orders_2(sK2),X0)
        | ~ r2_hidden(sK3,X0)
        | ~ r2_hidden(sK4,X0) )
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl8_5
  <=> ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ r4_relat_2(u1_orders_2(sK2),X0)
        | ~ r2_hidden(sK4,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f181,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | spl8_4 ),
    inference(subsumption_resolution,[],[f179,f42])).

fof(f179,plain,
    ( ~ l1_orders_2(sK2)
    | spl8_4 ),
    inference(resolution,[],[f178,f97])).

fof(f97,plain,(
    ! [X1] :
      ( v1_relat_1(u1_orders_2(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(subsumption_resolution,[],[f95,f65])).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f95,plain,(
    ! [X1] :
      ( ~ l1_orders_2(X1)
      | v1_relat_1(u1_orders_2(X1))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))) ) ),
    inference(resolution,[],[f48,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f48,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f178,plain,
    ( ~ v1_relat_1(u1_orders_2(sK2))
    | spl8_4 ),
    inference(resolution,[],[f163,f62])).

fof(f62,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f19,f24,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2,X3] :
          ( X2 = X3
          | ~ r2_hidden(k4_tarski(X3,X2),X0)
          | ~ r2_hidden(k4_tarski(X2,X3),X0)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).

fof(f163,plain,
    ( ~ sP1(u1_orders_2(sK2))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl8_4
  <=> sP1(u1_orders_2(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f173,plain,
    ( ~ spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f172,f165,f161])).

fof(f172,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r2_hidden(sK3,X1)
      | ~ r4_relat_2(u1_orders_2(sK2),X1)
      | ~ sP1(u1_orders_2(sK2)) ) ),
    inference(subsumption_resolution,[],[f171,f42])).

fof(f171,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ l1_orders_2(sK2)
      | ~ r2_hidden(sK3,X1)
      | ~ r4_relat_2(u1_orders_2(sK2),X1)
      | ~ sP1(u1_orders_2(sK2)) ) ),
    inference(subsumption_resolution,[],[f170,f43])).

fof(f43,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f170,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ r2_hidden(sK3,X1)
      | ~ r4_relat_2(u1_orders_2(sK2),X1)
      | ~ sP1(u1_orders_2(sK2)) ) ),
    inference(subsumption_resolution,[],[f169,f44])).

fof(f44,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f169,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ r2_hidden(sK3,X1)
      | ~ r4_relat_2(u1_orders_2(sK2),X1)
      | ~ sP1(u1_orders_2(sK2)) ) ),
    inference(subsumption_resolution,[],[f168,f45])).

fof(f45,plain,(
    r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f168,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | ~ r1_orders_2(sK2,sK3,sK4)
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ r2_hidden(sK3,X1)
      | ~ r4_relat_2(u1_orders_2(sK2),X1)
      | ~ sP1(u1_orders_2(sK2)) ) ),
    inference(subsumption_resolution,[],[f150,f47])).

fof(f47,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f29])).

fof(f150,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4,X1)
      | sK3 = sK4
      | ~ r1_orders_2(sK2,sK3,sK4)
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ r2_hidden(sK3,X1)
      | ~ r4_relat_2(u1_orders_2(sK2),X1)
      | ~ sP1(u1_orders_2(sK2)) ) ),
    inference(resolution,[],[f148,f46])).

fof(f46,plain,(
    r1_orders_2(sK2,sK4,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f148,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_orders_2(X11,X10,X8)
      | ~ r2_hidden(X10,X9)
      | X8 = X10
      | ~ r1_orders_2(X11,X8,X10)
      | ~ m1_subset_1(X10,u1_struct_0(X11))
      | ~ m1_subset_1(X8,u1_struct_0(X11))
      | ~ l1_orders_2(X11)
      | ~ r2_hidden(X8,X9)
      | ~ r4_relat_2(u1_orders_2(X11),X9)
      | ~ sP1(u1_orders_2(X11)) ) ),
    inference(resolution,[],[f145,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | ~ r4_relat_2(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f145,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(u1_orders_2(X3),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | X0 = X1
      | ~ r1_orders_2(X3,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X3))
      | ~ m1_subset_1(X1,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ r1_orders_2(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X1
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | ~ sP0(u1_orders_2(X3),X2)
      | ~ r1_orders_2(X3,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X3))
      | ~ m1_subset_1(X1,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ r1_orders_2(X3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X3))
      | ~ m1_subset_1(X0,u1_struct_0(X3))
      | ~ l1_orders_2(X3) ) ),
    inference(resolution,[],[f131,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f131,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(k4_tarski(X6,X7),u1_orders_2(X8))
      | X6 = X7
      | ~ r2_hidden(X7,X9)
      | ~ r2_hidden(X6,X9)
      | ~ sP0(u1_orders_2(X8),X9)
      | ~ r1_orders_2(X8,X7,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X8))
      | ~ m1_subset_1(X7,u1_struct_0(X8))
      | ~ l1_orders_2(X8) ) ),
    inference(resolution,[],[f56,f51])).

fof(f56,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X5,X4),X0)
      | X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK5(X0,X1) != sK6(X0,X1)
          & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
          & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
          & r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X1) ) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | ~ r2_hidden(k4_tarski(X5,X4),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & r2_hidden(k4_tarski(X3,X2),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( sK5(X0,X1) != sK6(X0,X1)
        & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
        & r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X3,X2),X0)
            & r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | ~ r2_hidden(k4_tarski(X5,X4),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X3,X2),X0)
            & r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f122,plain,(
    ~ spl8_2 ),
    inference(avatar_split_clause,[],[f119,f81])).

fof(f81,plain,
    ( spl8_2
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f119,plain,(
    ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f118,f42])).

fof(f118,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f114,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(resolution,[],[f48,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f114,plain,(
    ~ v1_xboole_0(u1_orders_2(sK2)) ),
    inference(subsumption_resolution,[],[f113,f42])).

fof(f113,plain,
    ( ~ l1_orders_2(sK2)
    | ~ v1_xboole_0(u1_orders_2(sK2)) ),
    inference(subsumption_resolution,[],[f112,f43])).

fof(f112,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ v1_xboole_0(u1_orders_2(sK2)) ),
    inference(subsumption_resolution,[],[f110,f44])).

fof(f110,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2)
    | ~ v1_xboole_0(u1_orders_2(sK2)) ),
    inference(resolution,[],[f109,f45])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_xboole_0(u1_orders_2(X0)) ) ),
    inference(resolution,[],[f51,f63])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f89,plain,
    ( spl8_3
    | spl8_2 ),
    inference(avatar_split_clause,[],[f75,f81,f86])).

fof(f75,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f67,f44])).

% (1183)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f84,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f74,f81,f77])).

fof(f74,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f67,f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 17:57:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.50  % (1174)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (1175)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (1173)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (1173)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f84,f89,f122,f173,f181,f191])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    ~spl8_1 | ~spl8_3 | ~spl8_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    $false | (~spl8_1 | ~spl8_3 | ~spl8_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f189,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    l1_orders_2(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ((sK3 != sK4 & r1_orders_2(sK2,sK4,sK3) & r1_orders_2(sK2,sK3,sK4) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f13,f28,f27,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0)) => (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(sK2,X2,X1) & r1_orders_2(sK2,X1,X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(sK2,X2,X1) & r1_orders_2(sK2,X1,X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : (sK3 != X2 & r1_orders_2(sK2,X2,sK3) & r1_orders_2(sK2,sK3,X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ? [X2] : (sK3 != X2 & r1_orders_2(sK2,X2,sK3) & r1_orders_2(sK2,sK3,X2) & m1_subset_1(X2,u1_struct_0(sK2))) => (sK3 != sK4 & r1_orders_2(sK2,sK4,sK3) & r1_orders_2(sK2,sK3,sK4) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((X1 != X2 & (r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    ~l1_orders_2(sK2) | (~spl8_1 | ~spl8_3 | ~spl8_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f188,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    v5_orders_2(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    ~v5_orders_2(sK2) | ~l1_orders_2(sK2) | (~spl8_1 | ~spl8_3 | ~spl8_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f187,f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    r2_hidden(sK4,u1_struct_0(sK2)) | ~spl8_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl8_3 <=> r2_hidden(sK4,u1_struct_0(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    ~r2_hidden(sK4,u1_struct_0(sK2)) | ~v5_orders_2(sK2) | ~l1_orders_2(sK2) | (~spl8_1 | ~spl8_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f184,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    r2_hidden(sK3,u1_struct_0(sK2)) | ~spl8_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl8_1 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ~r2_hidden(sK3,u1_struct_0(sK2)) | ~r2_hidden(sK4,u1_struct_0(sK2)) | ~v5_orders_2(sK2) | ~l1_orders_2(sK2) | ~spl8_5),
% 0.21/0.51    inference(resolution,[],[f166,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0] : (r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : (((v5_orders_2(X0) | ~r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) & (r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v5_orders_2(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : ((v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => (v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ( ! [X0] : (~r4_relat_2(u1_orders_2(sK2),X0) | ~r2_hidden(sK3,X0) | ~r2_hidden(sK4,X0)) ) | ~spl8_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f165])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    spl8_5 <=> ! [X0] : (~r2_hidden(sK3,X0) | ~r4_relat_2(u1_orders_2(sK2),X0) | ~r2_hidden(sK4,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    spl8_4),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f180])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    $false | spl8_4),
% 0.21/0.51    inference(subsumption_resolution,[],[f179,f42])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    ~l1_orders_2(sK2) | spl8_4),
% 0.21/0.51    inference(resolution,[],[f178,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ( ! [X1] : (v1_relat_1(u1_orders_2(X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f95,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X1] : (~l1_orders_2(X1) | v1_relat_1(u1_orders_2(X1)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) )),
% 0.21/0.51    inference(resolution,[],[f48,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    ~v1_relat_1(u1_orders_2(sK2)) | spl8_4),
% 0.21/0.51    inference(resolution,[],[f163,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0] : (sP1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(definition_folding,[],[f19,f24,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> sP0(X0,X1)) | ~sP1(X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | (~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : ((r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => X2 = X3)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ~sP1(u1_orders_2(sK2)) | spl8_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f161])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    spl8_4 <=> sP1(u1_orders_2(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ~spl8_4 | spl8_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f172,f165,f161])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r2_hidden(sK3,X1) | ~r4_relat_2(u1_orders_2(sK2),X1) | ~sP1(u1_orders_2(sK2))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f171,f42])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(sK4,X1) | ~l1_orders_2(sK2) | ~r2_hidden(sK3,X1) | ~r4_relat_2(u1_orders_2(sK2),X1) | ~sP1(u1_orders_2(sK2))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f170,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(sK4,X1) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~r2_hidden(sK3,X1) | ~r4_relat_2(u1_orders_2(sK2),X1) | ~sP1(u1_orders_2(sK2))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f169,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(sK4,X1) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~r2_hidden(sK3,X1) | ~r4_relat_2(u1_orders_2(sK2),X1) | ~sP1(u1_orders_2(sK2))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f168,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    r1_orders_2(sK2,sK3,sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(sK4,X1) | ~r1_orders_2(sK2,sK3,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~r2_hidden(sK3,X1) | ~r4_relat_2(u1_orders_2(sK2),X1) | ~sP1(u1_orders_2(sK2))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f150,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    sK3 != sK4),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(sK4,X1) | sK3 = sK4 | ~r1_orders_2(sK2,sK3,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~r2_hidden(sK3,X1) | ~r4_relat_2(u1_orders_2(sK2),X1) | ~sP1(u1_orders_2(sK2))) )),
% 0.21/0.51    inference(resolution,[],[f148,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    r1_orders_2(sK2,sK4,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    ( ! [X10,X8,X11,X9] : (~r1_orders_2(X11,X10,X8) | ~r2_hidden(X10,X9) | X8 = X10 | ~r1_orders_2(X11,X8,X10) | ~m1_subset_1(X10,u1_struct_0(X11)) | ~m1_subset_1(X8,u1_struct_0(X11)) | ~l1_orders_2(X11) | ~r2_hidden(X8,X9) | ~r4_relat_2(u1_orders_2(X11),X9) | ~sP1(u1_orders_2(X11))) )),
% 0.21/0.51    inference(resolution,[],[f145,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP0(X0,X1) | ~r4_relat_2(X0,X1) | ~sP1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((r4_relat_2(X0,X1) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~r4_relat_2(X0,X1))) | ~sP1(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f24])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~sP0(u1_orders_2(X3),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | X0 = X1 | ~r1_orders_2(X3,X1,X0) | ~m1_subset_1(X0,u1_struct_0(X3)) | ~m1_subset_1(X1,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~r1_orders_2(X3,X0,X1)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f142])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (X0 = X1 | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~sP0(u1_orders_2(X3),X2) | ~r1_orders_2(X3,X1,X0) | ~m1_subset_1(X0,u1_struct_0(X3)) | ~m1_subset_1(X1,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~r1_orders_2(X3,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X3)) | ~m1_subset_1(X0,u1_struct_0(X3)) | ~l1_orders_2(X3)) )),
% 0.21/0.51    inference(resolution,[],[f131,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ( ! [X6,X8,X7,X9] : (~r2_hidden(k4_tarski(X6,X7),u1_orders_2(X8)) | X6 = X7 | ~r2_hidden(X7,X9) | ~r2_hidden(X6,X9) | ~sP0(u1_orders_2(X8),X9) | ~r1_orders_2(X8,X7,X6) | ~m1_subset_1(X6,u1_struct_0(X8)) | ~m1_subset_1(X7,u1_struct_0(X8)) | ~l1_orders_2(X8)) )),
% 0.21/0.51    inference(resolution,[],[f56,f51])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X4,X0,X5,X1] : (~r2_hidden(k4_tarski(X5,X4),X0) | X4 = X5 | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~sP0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1] : ((sP0(X0,X1) | (sK5(X0,X1) != sK6(X0,X1) & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1))) & (! [X4,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f34,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (sK5(X0,X1) != sK6(X0,X1) & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~sP0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f23])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ~spl8_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f119,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    spl8_2 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ~v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f118,f42])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    ~l1_orders_2(sK2) | ~v1_xboole_0(u1_struct_0(sK2))),
% 0.21/0.51    inference(resolution,[],[f114,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X0] : (v1_xboole_0(u1_orders_2(X0)) | ~l1_orders_2(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.51    inference(resolution,[],[f48,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ~v1_xboole_0(u1_orders_2(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f113,f42])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ~l1_orders_2(sK2) | ~v1_xboole_0(u1_orders_2(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f112,f43])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~v1_xboole_0(u1_orders_2(sK2))),
% 0.21/0.51    inference(subsumption_resolution,[],[f110,f44])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~v1_xboole_0(u1_orders_2(sK2))),
% 0.21/0.51    inference(resolution,[],[f109,f45])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_xboole_0(u1_orders_2(X0))) )),
% 0.21/0.51    inference(resolution,[],[f51,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f38,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.51    inference(rectify,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    spl8_3 | spl8_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f75,f81,f86])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(sK4,u1_struct_0(sK2))),
% 0.21/0.51    inference(resolution,[],[f67,f44])).
% 0.21/0.51  % (1183)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl8_1 | spl8_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f74,f81,f77])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK2))),
% 0.21/0.51    inference(resolution,[],[f67,f43])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (1173)------------------------------
% 0.21/0.51  % (1173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1173)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (1173)Memory used [KB]: 6140
% 0.21/0.51  % (1173)Time elapsed: 0.061 s
% 0.21/0.51  % (1173)------------------------------
% 0.21/0.51  % (1173)------------------------------
% 0.21/0.51  % (1168)Success in time 0.138 s
%------------------------------------------------------------------------------
