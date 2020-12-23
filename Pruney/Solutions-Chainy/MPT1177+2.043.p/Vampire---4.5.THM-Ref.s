%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 732 expanded)
%              Number of leaves         :   20 ( 276 expanded)
%              Depth                    :   19
%              Number of atoms          :  765 (7213 expanded)
%              Number of equality atoms :   61 (  82 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f76,f145,f185,f207,f217,f223,f231,f239,f245])).

fof(f245,plain,
    ( ~ spl4_1
    | spl4_6
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl4_1
    | spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f243,f69])).

fof(f69,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl4_1
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f243,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f240,f143])).

fof(f143,plain,
    ( sK2 != sK3
    | spl4_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_6
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f240,plain,
    ( sK2 = sK3
    | ~ r2_xboole_0(sK2,sK3)
    | ~ spl4_8 ),
    inference(resolution,[],[f188,f79])).

fof(f79,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | X2 = X3
      | ~ r2_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f58,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f188,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl4_8
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f239,plain,
    ( spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f238,f138,f187])).

fof(f138,plain,
    ( spl4_5
  <=> m1_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f238,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f236,f43])).

fof(f43,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ m1_orders_2(sK2,sK0,sK3)
      | ~ r2_xboole_0(sK2,sK3) )
    & ( m1_orders_2(sK2,sK0,sK3)
      | r2_xboole_0(sK2,sK3) )
    & m2_orders_2(sK3,sK0,sK1)
    & m2_orders_2(sK2,sK0,sK1)
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_orders_2(X2,X0,X3)
                      | ~ r2_xboole_0(X2,X3) )
                    & ( m1_orders_2(X2,X0,X3)
                      | r2_xboole_0(X2,X3) )
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,sK0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK0,X1) )
              & m2_orders_2(X2,sK0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_orders_2(X2,sK0,X3)
                  | ~ r2_xboole_0(X2,X3) )
                & ( m1_orders_2(X2,sK0,X3)
                  | r2_xboole_0(X2,X3) )
                & m2_orders_2(X3,sK0,X1) )
            & m2_orders_2(X2,sK0,X1) )
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_orders_2(X2,sK0,X3)
                | ~ r2_xboole_0(X2,X3) )
              & ( m1_orders_2(X2,sK0,X3)
                | r2_xboole_0(X2,X3) )
              & m2_orders_2(X3,sK0,sK1) )
          & m2_orders_2(X2,sK0,sK1) )
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_orders_2(X2,sK0,X3)
              | ~ r2_xboole_0(X2,X3) )
            & ( m1_orders_2(X2,sK0,X3)
              | r2_xboole_0(X2,X3) )
            & m2_orders_2(X3,sK0,sK1) )
        & m2_orders_2(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ( ~ m1_orders_2(sK2,sK0,X3)
            | ~ r2_xboole_0(sK2,X3) )
          & ( m1_orders_2(sK2,sK0,X3)
            | r2_xboole_0(sK2,X3) )
          & m2_orders_2(X3,sK0,sK1) )
      & m2_orders_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ( ~ m1_orders_2(sK2,sK0,X3)
          | ~ r2_xboole_0(sK2,X3) )
        & ( m1_orders_2(sK2,sK0,X3)
          | r2_xboole_0(sK2,X3) )
        & m2_orders_2(X3,sK0,sK1) )
   => ( ( ~ m1_orders_2(sK2,sK0,sK3)
        | ~ r2_xboole_0(sK2,sK3) )
      & ( m1_orders_2(sK2,sK0,sK3)
        | r2_xboole_0(sK2,sK3) )
      & m2_orders_2(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).

fof(f236,plain,
    ( ~ m2_orders_2(sK2,sK0,sK1)
    | r1_tarski(sK3,sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f139,f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X1,sK0,X0)
      | ~ m2_orders_2(X0,sK0,sK1)
      | r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f170,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | v2_struct_0(sK0)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f169,f38])).

fof(f38,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f168,f39])).

fof(f39,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f167,f40])).

fof(f40,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f166,f41])).

fof(f41,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f106,f42])).

fof(f42,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f106,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
      | ~ m2_orders_2(X2,X3,X4)
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3)
      | ~ m1_orders_2(X5,X3,X2)
      | r1_tarski(X5,X2) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m2_orders_2(X2,X3,X4)
      | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3)
      | ~ m1_orders_2(X5,X3,X2)
      | r1_tarski(X5,X2)
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f55,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f139,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f138])).

fof(f231,plain,
    ( spl4_5
    | spl4_6
    | spl4_2 ),
    inference(avatar_split_clause,[],[f230,f72,f142,f138])).

fof(f72,plain,
    ( spl4_2
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f230,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f229,f43])).

fof(f229,plain,
    ( sK2 = sK3
    | ~ m2_orders_2(sK2,sK0,sK1)
    | m1_orders_2(sK3,sK0,sK2)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f228,f44])).

fof(f44,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f228,plain,
    ( sK2 = sK3
    | ~ m2_orders_2(sK3,sK0,sK1)
    | ~ m2_orders_2(sK2,sK0,sK1)
    | m1_orders_2(sK3,sK0,sK2)
    | spl4_2 ),
    inference(resolution,[],[f74,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( m1_orders_2(X1,sK0,X0)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | m1_orders_2(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f157,f37])).

fof(f157,plain,(
    ! [X0,X1] :
      ( m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | m1_orders_2(X1,sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f156,f38])).

fof(f156,plain,(
    ! [X0,X1] :
      ( m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | m1_orders_2(X1,sK0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f155,f39])).

fof(f155,plain,(
    ! [X0,X1] :
      ( m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | m1_orders_2(X1,sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f154,f40])).

fof(f154,plain,(
    ! [X0,X1] :
      ( m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | m1_orders_2(X1,sK0,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f153,f41])).

fof(f153,plain,(
    ! [X0,X1] :
      ( m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | m1_orders_2(X1,sK0,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f53,f42])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | m1_orders_2(X2,X0,X3)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

% (25599)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_orders_2(X2,X0,X3)
                      | m1_orders_2(X3,X0,X2) )
                    & ( ~ m1_orders_2(X3,X0,X2)
                      | ~ m1_orders_2(X2,X0,X3) ) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).

fof(f74,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f223,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f222,f119])).

fof(f119,plain,
    ( spl4_4
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f222,plain,(
    ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f221,f37])).

fof(f221,plain,
    ( v2_struct_0(sK0)
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f220,f38])).

fof(f220,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f219,f39])).

fof(f219,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f218,f40])).

fof(f218,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f127,f41])).

fof(f127,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(resolution,[],[f124,f42])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m2_orders_2(k1_xboole_0,X1,X0) ) ),
    inference(resolution,[],[f123,f47])).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_funct_1(X2,u1_struct_0(X1)))
      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m2_orders_2(X0,X1,X2) ) ),
    inference(resolution,[],[f51,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

fof(f217,plain,
    ( spl4_4
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f214,f142,f72,f119])).

fof(f214,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f43,f201])).

fof(f201,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f199,f43])).

fof(f199,plain,
    ( k1_xboole_0 = sK2
    | ~ m2_orders_2(sK2,sK0,sK1)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(resolution,[],[f194,f152])).

fof(f152,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,X0)
      | k1_xboole_0 = X0
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f151,f37])).

fof(f151,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | v2_struct_0(sK0)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X0,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f150,f38])).

fof(f150,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X0,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f149,f39])).

fof(f149,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X0,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f148,f40])).

fof(f148,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X0,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f147,f41])).

fof(f147,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X0,sK0,X0) ) ),
    inference(resolution,[],[f105,f42])).

fof(f105,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_orders_1(X8,k1_orders_1(u1_struct_0(X7)))
      | ~ m2_orders_2(X6,X7,X8)
      | ~ l1_orders_2(X7)
      | ~ v5_orders_2(X7)
      | ~ v4_orders_2(X7)
      | ~ v3_orders_2(X7)
      | v2_struct_0(X7)
      | k1_xboole_0 = X6
      | ~ m1_orders_2(X6,X7,X6) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X6,X8,X7] :
      ( ~ m2_orders_2(X6,X7,X8)
      | ~ m1_orders_1(X8,k1_orders_1(u1_struct_0(X7)))
      | ~ l1_orders_2(X7)
      | ~ v5_orders_2(X7)
      | ~ v4_orders_2(X7)
      | ~ v3_orders_2(X7)
      | v2_struct_0(X7)
      | k1_xboole_0 = X6
      | ~ m1_orders_2(X6,X7,X6)
      | ~ l1_orders_2(X7)
      | ~ v5_orders_2(X7)
      | ~ v4_orders_2(X7)
      | ~ v3_orders_2(X7)
      | v2_struct_0(X7) ) ),
    inference(resolution,[],[f55,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X1,X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k1_xboole_0 != X1
              | m1_orders_2(X1,X0,X1) )
            & ( ~ m1_orders_2(X1,X0,X1)
              | k1_xboole_0 = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k1_xboole_0 != X1
              | m1_orders_2(X1,X0,X1) )
            & ( ~ m1_orders_2(X1,X0,X1)
              | k1_xboole_0 = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
            & ~ ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).

fof(f194,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f73,f144])).

fof(f144,plain,
    ( sK2 = sK3
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f73,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f207,plain,
    ( ~ spl4_1
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f205,f66])).

fof(f66,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f205,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f69,f144])).

fof(f185,plain,
    ( spl4_6
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f184,f72,f68,f142])).

fof(f184,plain,
    ( sK2 = sK3
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f177,f70])).

fof(f70,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f177,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK2,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f175,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f175,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f172,f44])).

fof(f172,plain,
    ( ~ m2_orders_2(sK3,sK0,sK1)
    | r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f171,f73])).

fof(f145,plain,
    ( ~ spl4_5
    | spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f136,f72,f142,f138])).

fof(f136,plain,
    ( sK2 = sK3
    | ~ m1_orders_2(sK3,sK0,sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f135,f44])).

fof(f135,plain,
    ( sK2 = sK3
    | ~ m2_orders_2(sK3,sK0,sK1)
    | ~ m1_orders_2(sK3,sK0,sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f134,f43])).

fof(f134,plain,
    ( sK2 = sK3
    | ~ m2_orders_2(sK2,sK0,sK1)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | ~ m1_orders_2(sK3,sK0,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f133,f73])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X1,sK0,X0)
      | X0 = X1
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f132,f37])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f131,f38])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f130,f39])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f129,f40])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f128,f41])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f52,f42])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X3)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_2(X3,X0,X2)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f45,f72,f68])).

fof(f45,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f46,f72,f68])).

fof(f46,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (25598)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.49  % (25594)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (25585)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (25606)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.49  % (25600)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (25585)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f75,f76,f145,f185,f207,f217,f223,f231,f239,f245])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    ~spl4_1 | spl4_6 | ~spl4_8),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f244])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    $false | (~spl4_1 | spl4_6 | ~spl4_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f243,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    r2_xboole_0(sK2,sK3) | ~spl4_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    spl4_1 <=> r2_xboole_0(sK2,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    ~r2_xboole_0(sK2,sK3) | (spl4_6 | ~spl4_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f240,f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    sK2 != sK3 | spl4_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f142])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    spl4_6 <=> sK2 = sK3),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    sK2 = sK3 | ~r2_xboole_0(sK2,sK3) | ~spl4_8),
% 0.21/0.50    inference(resolution,[],[f188,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~r1_tarski(X2,X3) | X2 = X3 | ~r2_xboole_0(X3,X2)) )),
% 0.21/0.50    inference(resolution,[],[f58,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.50    inference(flattening,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    r1_tarski(sK3,sK2) | ~spl4_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f187])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    spl4_8 <=> r1_tarski(sK3,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    spl4_8 | ~spl4_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f238,f138,f187])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl4_5 <=> m1_orders_2(sK3,sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    r1_tarski(sK3,sK2) | ~spl4_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f236,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    m2_orders_2(sK2,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f30,f29,f28,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) => ((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_orders_2)).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    ~m2_orders_2(sK2,sK0,sK1) | r1_tarski(sK3,sK2) | ~spl4_5),
% 0.21/0.50    inference(resolution,[],[f139,f171])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_orders_2(X1,sK0,X0) | ~m2_orders_2(X0,sK0,sK1) | r1_tarski(X1,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f170,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | v2_struct_0(sK0) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f169,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    v3_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f168,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    v4_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f167,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    v5_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f166,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    l1_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f106,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ( ! [X4,X2,X5,X3] : (~m1_orders_1(X4,k1_orders_1(u1_struct_0(X3))) | ~m2_orders_2(X2,X3,X4) | ~l1_orders_2(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | v2_struct_0(X3) | ~m1_orders_2(X5,X3,X2) | r1_tarski(X5,X2)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ( ! [X4,X2,X5,X3] : (~m2_orders_2(X2,X3,X4) | ~m1_orders_1(X4,k1_orders_1(u1_struct_0(X3))) | ~l1_orders_2(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | v2_struct_0(X3) | ~m1_orders_2(X5,X3,X2) | r1_tarski(X5,X2) | ~l1_orders_2(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | v2_struct_0(X3)) )),
% 0.21/0.50    inference(resolution,[],[f55,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_orders_2)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    m1_orders_2(sK3,sK0,sK2) | ~spl4_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f138])).
% 0.21/0.50  fof(f231,plain,(
% 0.21/0.50    spl4_5 | spl4_6 | spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f230,f72,f142,f138])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl4_2 <=> m1_orders_2(sK2,sK0,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    sK2 = sK3 | m1_orders_2(sK3,sK0,sK2) | spl4_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f229,f43])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    sK2 = sK3 | ~m2_orders_2(sK2,sK0,sK1) | m1_orders_2(sK3,sK0,sK2) | spl4_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f228,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    m2_orders_2(sK3,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    sK2 = sK3 | ~m2_orders_2(sK3,sK0,sK1) | ~m2_orders_2(sK2,sK0,sK1) | m1_orders_2(sK3,sK0,sK2) | spl4_2),
% 0.21/0.50    inference(resolution,[],[f74,f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_orders_2(X1,sK0,X0) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X0,sK0,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f157,f37])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X1,sK0,X0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f156,f38])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X1,sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f155,f39])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X1,sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f154,f40])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X1,sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f153,f41])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X1,sK0,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f53,f42])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | m1_orders_2(X2,X0,X3) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  % (25599)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_orders_2)).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ~m1_orders_2(sK2,sK0,sK3) | spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ~spl4_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f222,f119])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl4_4 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    ~m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f221,f37])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f220,f38])).
% 0.21/0.50  fof(f220,plain,(
% 0.21/0.50    ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f219,f39])).
% 0.21/0.50  fof(f219,plain,(
% 0.21/0.50    ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f218,f40])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f127,f41])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f124,f42])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | ~m2_orders_2(k1_xboole_0,X1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f123,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_funct_1(X2,u1_struct_0(X1))) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | ~m2_orders_2(X0,X1,X2)) )),
% 0.21/0.50    inference(resolution,[],[f51,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).
% 0.21/0.50  fof(f217,plain,(
% 0.21/0.50    spl4_4 | ~spl4_2 | ~spl4_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f214,f142,f72,f119])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    m2_orders_2(k1_xboole_0,sK0,sK1) | (~spl4_2 | ~spl4_6)),
% 0.21/0.50    inference(backward_demodulation,[],[f43,f201])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | (~spl4_2 | ~spl4_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f199,f43])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | ~m2_orders_2(sK2,sK0,sK1) | (~spl4_2 | ~spl4_6)),
% 0.21/0.50    inference(resolution,[],[f194,f152])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_orders_2(X0,sK0,X0) | k1_xboole_0 = X0 | ~m2_orders_2(X0,sK0,sK1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f151,f37])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | v2_struct_0(sK0) | k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f150,f38])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f149,f39])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f148,f40])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f147,f41])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,X0)) )),
% 0.21/0.50    inference(resolution,[],[f105,f42])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ( ! [X6,X8,X7] : (~m1_orders_1(X8,k1_orders_1(u1_struct_0(X7))) | ~m2_orders_2(X6,X7,X8) | ~l1_orders_2(X7) | ~v5_orders_2(X7) | ~v4_orders_2(X7) | ~v3_orders_2(X7) | v2_struct_0(X7) | k1_xboole_0 = X6 | ~m1_orders_2(X6,X7,X6)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f104])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ( ! [X6,X8,X7] : (~m2_orders_2(X6,X7,X8) | ~m1_orders_1(X8,k1_orders_1(u1_struct_0(X7))) | ~l1_orders_2(X7) | ~v5_orders_2(X7) | ~v4_orders_2(X7) | ~v3_orders_2(X7) | v2_struct_0(X7) | k1_xboole_0 = X6 | ~m1_orders_2(X6,X7,X6) | ~l1_orders_2(X7) | ~v5_orders_2(X7) | ~v4_orders_2(X7) | ~v3_orders_2(X7) | v2_struct_0(X7)) )),
% 0.21/0.50    inference(resolution,[],[f55,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | ~m1_orders_2(X1,X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    m1_orders_2(sK2,sK0,sK2) | (~spl4_2 | ~spl4_6)),
% 0.21/0.50    inference(backward_demodulation,[],[f73,f144])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    sK2 = sK3 | ~spl4_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f142])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    m1_orders_2(sK2,sK0,sK3) | ~spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ~spl4_1 | ~spl4_6),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f206])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    $false | (~spl4_1 | ~spl4_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f205,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    r2_xboole_0(sK2,sK2) | (~spl4_1 | ~spl4_6)),
% 0.21/0.50    inference(forward_demodulation,[],[f69,f144])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    spl4_6 | spl4_1 | ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f184,f72,f68,f142])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    sK2 = sK3 | (spl4_1 | ~spl4_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f177,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ~r2_xboole_0(sK2,sK3) | spl4_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f68])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    sK2 = sK3 | r2_xboole_0(sK2,sK3) | ~spl4_2),
% 0.21/0.50    inference(resolution,[],[f175,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    r1_tarski(sK2,sK3) | ~spl4_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f172,f44])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ~m2_orders_2(sK3,sK0,sK1) | r1_tarski(sK2,sK3) | ~spl4_2),
% 0.21/0.50    inference(resolution,[],[f171,f73])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    ~spl4_5 | spl4_6 | ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f136,f72,f142,f138])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    sK2 = sK3 | ~m1_orders_2(sK3,sK0,sK2) | ~spl4_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f135,f44])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    sK2 = sK3 | ~m2_orders_2(sK3,sK0,sK1) | ~m1_orders_2(sK3,sK0,sK2) | ~spl4_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f134,f43])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    sK2 = sK3 | ~m2_orders_2(sK2,sK0,sK1) | ~m2_orders_2(sK3,sK0,sK1) | ~m1_orders_2(sK3,sK0,sK2) | ~spl4_2),
% 0.21/0.50    inference(resolution,[],[f133,f73])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_orders_2(X1,sK0,X0) | X0 = X1 | ~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X0,sK0,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f132,f37])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f131,f38])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f130,f39])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f129,f40])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f128,f41])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f52,f42])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X3) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_2(X3,X0,X2) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl4_1 | spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f72,f68])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ~spl4_1 | ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f72,f68])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (25585)------------------------------
% 0.21/0.50  % (25585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25585)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (25585)Memory used [KB]: 6268
% 0.21/0.50  % (25585)Time elapsed: 0.088 s
% 0.21/0.50  % (25585)------------------------------
% 0.21/0.50  % (25585)------------------------------
% 0.21/0.50  % (25596)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (25584)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (25582)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (25601)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (25580)Success in time 0.148 s
%------------------------------------------------------------------------------
