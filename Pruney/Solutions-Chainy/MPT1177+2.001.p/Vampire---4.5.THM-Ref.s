%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  177 (1038 expanded)
%              Number of leaves         :   21 ( 384 expanded)
%              Depth                    :   27
%              Number of atoms          :  979 (10351 expanded)
%              Number of equality atoms :   70 ( 100 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f428,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f82,f99,f129,f196,f200,f204,f306,f323,f342,f397,f427])).

fof(f427,plain,
    ( ~ spl5_1
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | ~ spl5_1
    | spl5_4 ),
    inference(subsumption_resolution,[],[f425,f97])).

fof(f97,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_4
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f425,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl5_1 ),
    inference(resolution,[],[f75,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f75,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_1
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f397,plain,(
    ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f396])).

fof(f396,plain,
    ( $false
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f395,f351])).

fof(f351,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl5_9 ),
    inference(superposition,[],[f45,f219])).

fof(f219,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl5_9
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f45,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f27,f26,f25,f24])).

fof(f24,plain,
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

fof(f25,plain,
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

fof(f26,plain,
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

fof(f27,plain,
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).

fof(f395,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl5_9 ),
    inference(resolution,[],[f394,f44])).

fof(f44,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f394,plain,
    ( ! [X0] :
        ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(k1_xboole_0,sK0,X0) )
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f393,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f393,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f392,f40])).

fof(f40,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f392,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f391,f41])).

fof(f41,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f391,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f390,f42])).

fof(f42,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f390,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f389,f43])).

fof(f43,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f389,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f384,f353])).

fof(f353,plain,
    ( v6_orders_2(k1_xboole_0,sK0)
    | ~ spl5_9 ),
    inference(superposition,[],[f107,f219])).

fof(f107,plain,(
    v6_orders_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f106,f39])).

fof(f106,plain,
    ( v6_orders_2(sK2,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f105,f40])).

fof(f105,plain,
    ( v6_orders_2(sK2,sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f104,f41])).

fof(f104,plain,
    ( v6_orders_2(sK2,sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f103,f42])).

fof(f103,plain,
    ( v6_orders_2(sK2,sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f102,f43])).

fof(f102,plain,
    ( v6_orders_2(sK2,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f100,f44])).

fof(f100,plain,
    ( v6_orders_2(sK2,sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f60,f45])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_orders_2(X2,X0,X1)
      | v6_orders_2(X2,X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f384,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ v6_orders_2(k1_xboole_0,sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f354,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(k1_xboole_0,X0,X1)
      | ~ v6_orders_2(k1_xboole_0,X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X2,X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ( sK4(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK4(X0,X1,X2))))
                    & r2_hidden(sK4(X0,X1,X2),X2)
                    & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X4] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK4(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK4(X0,X1,X2))))
        & r2_hidden(sK4(X0,X1,X2),X2)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X4] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X3] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                        | ~ r2_hidden(X3,X2)
                        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X3] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                        | ~ r2_hidden(X3,X2)
                        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X2,X0) )
             => ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 ) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).

fof(f354,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_9 ),
    inference(superposition,[],[f121,f219])).

% (615)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f121,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f120,f39])).

fof(f120,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f119,f40])).

fof(f119,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f118,f41])).

fof(f118,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f117,f42])).

fof(f117,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f116,f43])).

fof(f116,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f114,f44])).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f61,f45])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f342,plain,
    ( ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7 ),
    inference(global_subsumption,[],[f310,f340])).

fof(f340,plain,
    ( ~ m1_orders_2(sK2,sK0,sK2)
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7 ),
    inference(forward_demodulation,[],[f170,f307])).

fof(f307,plain,
    ( sK2 = sK3
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(global_subsumption,[],[f166])).

fof(f166,plain,
    ( sK2 = sK3
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl5_6
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f170,plain,
    ( ~ m1_orders_2(sK3,sK0,sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl5_7
  <=> m1_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f310,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f79,f307])).

fof(f79,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_2
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f323,plain,
    ( ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9 ),
    inference(subsumption_resolution,[],[f321,f39])).

fof(f321,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9 ),
    inference(subsumption_resolution,[],[f320,f40])).

fof(f320,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9 ),
    inference(subsumption_resolution,[],[f319,f41])).

fof(f319,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9 ),
    inference(subsumption_resolution,[],[f318,f42])).

fof(f318,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9 ),
    inference(subsumption_resolution,[],[f317,f43])).

fof(f317,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9 ),
    inference(subsumption_resolution,[],[f316,f121])).

fof(f316,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7
    | spl5_9 ),
    inference(subsumption_resolution,[],[f312,f218])).

fof(f218,plain,
    ( k1_xboole_0 != sK2
    | spl5_9 ),
    inference(avatar_component_clause,[],[f217])).

fof(f312,plain,
    ( k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(resolution,[],[f308,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X1,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

% (602)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f6])).

% (600)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).

fof(f308,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f169,f307])).

fof(f169,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f168])).

fof(f306,plain,
    ( spl5_2
    | spl5_6
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | spl5_2
    | spl5_6
    | spl5_8 ),
    inference(subsumption_resolution,[],[f304,f39])).

fof(f304,plain,
    ( v2_struct_0(sK0)
    | spl5_2
    | spl5_6
    | spl5_8 ),
    inference(subsumption_resolution,[],[f303,f40])).

fof(f303,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_2
    | spl5_6
    | spl5_8 ),
    inference(subsumption_resolution,[],[f302,f41])).

fof(f302,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_2
    | spl5_6
    | spl5_8 ),
    inference(subsumption_resolution,[],[f301,f42])).

fof(f301,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_2
    | spl5_6
    | spl5_8 ),
    inference(subsumption_resolution,[],[f300,f43])).

fof(f300,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_2
    | spl5_6
    | spl5_8 ),
    inference(subsumption_resolution,[],[f299,f121])).

fof(f299,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_2
    | spl5_6
    | spl5_8 ),
    inference(subsumption_resolution,[],[f298,f195])).

fof(f195,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl5_8
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f298,plain,
    ( r1_tarski(sK3,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_2
    | spl5_6 ),
    inference(resolution,[],[f293,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
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
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(f293,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | spl5_2
    | spl5_6 ),
    inference(subsumption_resolution,[],[f289,f80])).

fof(f80,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f289,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3)
    | spl5_6 ),
    inference(subsumption_resolution,[],[f287,f165])).

% (596)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (598)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f165,plain,
    ( sK2 != sK3
    | spl5_6 ),
    inference(avatar_component_clause,[],[f164])).

fof(f287,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(resolution,[],[f179,f46])).

fof(f46,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f179,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | m1_orders_2(sK2,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f178,f39])).

fof(f178,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f177,f40])).

fof(f177,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f176,f41])).

fof(f176,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f175,f42])).

fof(f175,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f174,f43])).

fof(f174,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f172,f44])).

fof(f172,plain,(
    ! [X0] :
      ( m1_orders_2(sK2,sK0,X0)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f50,f45])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m2_orders_2(X3,X0,X1)
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | m1_orders_2(X2,X0,X3)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).

fof(f204,plain,
    ( ~ spl5_1
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f202,f72])).

fof(f72,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f202,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl5_1
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f75,f166])).

fof(f200,plain,
    ( spl5_1
    | ~ spl5_4
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | spl5_1
    | ~ spl5_4
    | spl5_8 ),
    inference(subsumption_resolution,[],[f198,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f198,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl5_1
    | ~ spl5_4
    | spl5_8 ),
    inference(forward_demodulation,[],[f195,f197])).

fof(f197,plain,
    ( sK2 = sK3
    | spl5_1
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f186,f76])).

fof(f76,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f186,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK2,sK3)
    | ~ spl5_4 ),
    inference(resolution,[],[f98,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f196,plain,
    ( ~ spl5_8
    | spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f187,f96,f164,f193])).

fof(f187,plain,
    ( sK2 = sK3
    | ~ r1_tarski(sK3,sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f98,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f129,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl5_3 ),
    inference(subsumption_resolution,[],[f127,f39])).

fof(f127,plain,
    ( v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f126,f40])).

fof(f126,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f125,f41])).

fof(f125,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f124,f42])).

% (602)Refutation not found, incomplete strategy% (602)------------------------------
% (602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f124,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f123,f43])).

% (602)Termination reason: Refutation not found, incomplete strategy

% (602)Memory used [KB]: 10618
% (602)Time elapsed: 0.099 s
% (602)------------------------------
% (602)------------------------------
fof(f123,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f122,f44])).

fof(f122,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(subsumption_resolution,[],[f115,f94])).

fof(f94,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f115,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f61,f46])).

fof(f99,plain,
    ( ~ spl5_3
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f90,f78,f96,f92])).

fof(f90,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f89,f39])).

fof(f89,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f88,f40])).

fof(f88,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f87,f41])).

fof(f87,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f86,f42])).

fof(f86,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f85,f43])).

fof(f85,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f59,f79])).

fof(f82,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f47,f78,f74])).

fof(f47,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f48,f78,f74])).

fof(f48,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:20:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (610)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (599)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.49  % (606)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.49  % (611)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (606)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f428,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f81,f82,f99,f129,f196,f200,f204,f306,f323,f342,f397,f427])).
% 0.22/0.50  fof(f427,plain,(
% 0.22/0.50    ~spl5_1 | spl5_4),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f426])).
% 0.22/0.50  fof(f426,plain,(
% 0.22/0.50    $false | (~spl5_1 | spl5_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f425,f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ~r1_tarski(sK2,sK3) | spl5_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    spl5_4 <=> r1_tarski(sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.50  fof(f425,plain,(
% 0.22/0.50    r1_tarski(sK2,sK3) | ~spl5_1),
% 0.22/0.50    inference(resolution,[],[f75,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.50    inference(flattening,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    r2_xboole_0(sK2,sK3) | ~spl5_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl5_1 <=> r2_xboole_0(sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.50  fof(f397,plain,(
% 0.22/0.50    ~spl5_9),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f396])).
% 0.22/0.50  fof(f396,plain,(
% 0.22/0.50    $false | ~spl5_9),
% 0.22/0.50    inference(subsumption_resolution,[],[f395,f351])).
% 0.22/0.50  fof(f351,plain,(
% 0.22/0.50    m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl5_9),
% 0.22/0.50    inference(superposition,[],[f45,f219])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | ~spl5_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f217])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    spl5_9 <=> k1_xboole_0 = sK2),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    m2_orders_2(sK2,sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f27,f26,f25,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) => ((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f8])).
% 0.22/0.50  fof(f8,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).
% 0.22/0.50  fof(f395,plain,(
% 0.22/0.50    ~m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl5_9),
% 0.22/0.50    inference(resolution,[],[f394,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f394,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(k1_xboole_0,sK0,X0)) ) | ~spl5_9),
% 0.22/0.50    inference(subsumption_resolution,[],[f393,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f393,plain,(
% 0.22/0.50    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | ~spl5_9),
% 0.22/0.50    inference(subsumption_resolution,[],[f392,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    v3_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f392,plain,(
% 0.22/0.50    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_9),
% 0.22/0.50    inference(subsumption_resolution,[],[f391,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    v4_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f391,plain,(
% 0.22/0.50    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_9),
% 0.22/0.50    inference(subsumption_resolution,[],[f390,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    v5_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f390,plain,(
% 0.22/0.50    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_9),
% 0.22/0.50    inference(subsumption_resolution,[],[f389,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    l1_orders_2(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f389,plain,(
% 0.22/0.50    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_9),
% 0.22/0.50    inference(subsumption_resolution,[],[f384,f353])).
% 0.22/0.50  fof(f353,plain,(
% 0.22/0.50    v6_orders_2(k1_xboole_0,sK0) | ~spl5_9),
% 0.22/0.50    inference(superposition,[],[f107,f219])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    v6_orders_2(sK2,sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f106,f39])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    v6_orders_2(sK2,sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f105,f40])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    v6_orders_2(sK2,sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f104,f41])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    v6_orders_2(sK2,sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f103,f42])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    v6_orders_2(sK2,sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f102,f43])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    v6_orders_2(sK2,sK0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f100,f44])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    v6_orders_2(sK2,sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f60,f45])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m2_orders_2(X2,X0,X1) | v6_orders_2(X2,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.22/0.50  fof(f384,plain,(
% 0.22/0.50    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~v6_orders_2(k1_xboole_0,sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_9),
% 0.22/0.50    inference(resolution,[],[f354,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(k1_xboole_0,X0,X1) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (sK4(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK4(X0,X1,X2)))) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (sK4(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK4(X0,X1,X2)))) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(rectify,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2)) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).
% 0.22/0.50  fof(f354,plain,(
% 0.22/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_9),
% 0.22/0.50    inference(superposition,[],[f121,f219])).
% 0.22/0.50  % (615)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f120,f39])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f119,f40])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f118,f41])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f117,f42])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f116,f43])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f114,f44])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f61,f45])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f342,plain,(
% 0.22/0.50    ~spl5_2 | ~spl5_4 | ~spl5_6 | spl5_7),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f341])).
% 0.22/0.50  fof(f341,plain,(
% 0.22/0.50    $false | (~spl5_2 | ~spl5_4 | ~spl5_6 | spl5_7)),
% 0.22/0.50    inference(global_subsumption,[],[f310,f340])).
% 0.22/0.50  fof(f340,plain,(
% 0.22/0.50    ~m1_orders_2(sK2,sK0,sK2) | (~spl5_4 | ~spl5_6 | spl5_7)),
% 0.22/0.50    inference(forward_demodulation,[],[f170,f307])).
% 0.22/0.50  fof(f307,plain,(
% 0.22/0.50    sK2 = sK3 | (~spl5_4 | ~spl5_6)),
% 0.22/0.50    inference(global_subsumption,[],[f166])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    sK2 = sK3 | ~spl5_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f164])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    spl5_6 <=> sK2 = sK3),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    ~m1_orders_2(sK3,sK0,sK2) | spl5_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f168])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    spl5_7 <=> m1_orders_2(sK3,sK0,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.50  fof(f310,plain,(
% 0.22/0.50    m1_orders_2(sK2,sK0,sK2) | (~spl5_2 | ~spl5_4 | ~spl5_6)),
% 0.22/0.50    inference(forward_demodulation,[],[f79,f307])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    m1_orders_2(sK2,sK0,sK3) | ~spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl5_2 <=> m1_orders_2(sK2,sK0,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.50  fof(f323,plain,(
% 0.22/0.50    ~spl5_4 | ~spl5_6 | ~spl5_7 | spl5_9),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f322])).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    $false | (~spl5_4 | ~spl5_6 | ~spl5_7 | spl5_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f321,f39])).
% 0.22/0.50  fof(f321,plain,(
% 0.22/0.50    v2_struct_0(sK0) | (~spl5_4 | ~spl5_6 | ~spl5_7 | spl5_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f320,f40])).
% 0.22/0.50  fof(f320,plain,(
% 0.22/0.50    ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_6 | ~spl5_7 | spl5_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f319,f41])).
% 0.22/0.50  fof(f319,plain,(
% 0.22/0.50    ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_6 | ~spl5_7 | spl5_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f318,f42])).
% 0.22/0.50  fof(f318,plain,(
% 0.22/0.50    ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_6 | ~spl5_7 | spl5_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f317,f43])).
% 0.22/0.50  fof(f317,plain,(
% 0.22/0.50    ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_6 | ~spl5_7 | spl5_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f316,f121])).
% 0.22/0.50  fof(f316,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_6 | ~spl5_7 | spl5_9)),
% 0.22/0.50    inference(subsumption_resolution,[],[f312,f218])).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    k1_xboole_0 != sK2 | spl5_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f217])).
% 0.22/0.50  fof(f312,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.22/0.50    inference(resolution,[],[f308,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  % (602)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  % (600)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).
% 0.22/0.50  fof(f308,plain,(
% 0.22/0.50    m1_orders_2(sK2,sK0,sK2) | (~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.22/0.50    inference(forward_demodulation,[],[f169,f307])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    m1_orders_2(sK3,sK0,sK2) | ~spl5_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f168])).
% 0.22/0.50  fof(f306,plain,(
% 0.22/0.50    spl5_2 | spl5_6 | spl5_8),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f305])).
% 0.22/0.50  fof(f305,plain,(
% 0.22/0.50    $false | (spl5_2 | spl5_6 | spl5_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f304,f39])).
% 0.22/0.50  fof(f304,plain,(
% 0.22/0.50    v2_struct_0(sK0) | (spl5_2 | spl5_6 | spl5_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f303,f40])).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    ~v3_orders_2(sK0) | v2_struct_0(sK0) | (spl5_2 | spl5_6 | spl5_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f302,f41])).
% 0.22/0.50  fof(f302,plain,(
% 0.22/0.50    ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (spl5_2 | spl5_6 | spl5_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f301,f42])).
% 0.22/0.50  fof(f301,plain,(
% 0.22/0.50    ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (spl5_2 | spl5_6 | spl5_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f300,f43])).
% 0.22/0.50  fof(f300,plain,(
% 0.22/0.50    ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (spl5_2 | spl5_6 | spl5_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f299,f121])).
% 0.22/0.50  fof(f299,plain,(
% 0.22/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (spl5_2 | spl5_6 | spl5_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f298,f195])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    ~r1_tarski(sK3,sK2) | spl5_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f193])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    spl5_8 <=> r1_tarski(sK3,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.50  fof(f298,plain,(
% 0.22/0.50    r1_tarski(sK3,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | (spl5_2 | spl5_6)),
% 0.22/0.50    inference(resolution,[],[f293,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).
% 0.22/0.50  fof(f293,plain,(
% 0.22/0.50    m1_orders_2(sK3,sK0,sK2) | (spl5_2 | spl5_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f289,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    ~m1_orders_2(sK2,sK0,sK3) | spl5_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f78])).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    m1_orders_2(sK3,sK0,sK2) | m1_orders_2(sK2,sK0,sK3) | spl5_6),
% 0.22/0.50    inference(subsumption_resolution,[],[f287,f165])).
% 0.22/0.50  % (596)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (598)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    sK2 != sK3 | spl5_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f164])).
% 0.22/0.50  fof(f287,plain,(
% 0.22/0.50    sK2 = sK3 | m1_orders_2(sK3,sK0,sK2) | m1_orders_2(sK2,sK0,sK3)),
% 0.22/0.50    inference(resolution,[],[f179,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    m2_orders_2(sK3,sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f178,f39])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f177,f40])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f176,f41])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f175,f42])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f174,f43])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f172,f44])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    ( ! [X0] : (m1_orders_2(sK2,sK0,X0) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | ~m2_orders_2(X0,sK0,sK1) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.50    inference(resolution,[],[f50,f45])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m2_orders_2(X3,X0,X1) | m1_orders_2(X3,X0,X2) | X2 = X3 | m1_orders_2(X2,X0,X3) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    ~spl5_1 | ~spl5_6),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f203])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    $false | (~spl5_1 | ~spl5_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f202,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    r2_xboole_0(sK2,sK2) | (~spl5_1 | ~spl5_6)),
% 0.22/0.50    inference(forward_demodulation,[],[f75,f166])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    spl5_1 | ~spl5_4 | spl5_8),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f199])).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    $false | (spl5_1 | ~spl5_4 | spl5_8)),
% 0.22/0.50    inference(subsumption_resolution,[],[f198,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.50    inference(flattening,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    ~r1_tarski(sK2,sK2) | (spl5_1 | ~spl5_4 | spl5_8)),
% 0.22/0.50    inference(forward_demodulation,[],[f195,f197])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    sK2 = sK3 | (spl5_1 | ~spl5_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f186,f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ~r2_xboole_0(sK2,sK3) | spl5_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f74])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    sK2 = sK3 | r2_xboole_0(sK2,sK3) | ~spl5_4),
% 0.22/0.50    inference(resolution,[],[f98,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    r1_tarski(sK2,sK3) | ~spl5_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f96])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    ~spl5_8 | spl5_6 | ~spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f187,f96,f164,f193])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    sK2 = sK3 | ~r1_tarski(sK3,sK2) | ~spl5_4),
% 0.22/0.50    inference(resolution,[],[f98,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    spl5_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f128])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    $false | spl5_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f127,f39])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    v2_struct_0(sK0) | spl5_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f126,f40])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl5_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f125,f41])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl5_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f124,f42])).
% 0.22/0.50  % (602)Refutation not found, incomplete strategy% (602)------------------------------
% 0.22/0.50  % (602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl5_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f123,f43])).
% 0.22/0.50  % (602)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (602)Memory used [KB]: 10618
% 0.22/0.50  % (602)Time elapsed: 0.099 s
% 0.22/0.50  % (602)------------------------------
% 0.22/0.50  % (602)------------------------------
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl5_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f122,f44])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl5_3),
% 0.22/0.50    inference(subsumption_resolution,[],[f115,f94])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl5_3 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f61,f46])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ~spl5_3 | spl5_4 | ~spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f90,f78,f96,f92])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f89,f39])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl5_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f88,f40])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl5_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f87,f41])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl5_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f86,f42])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl5_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f85,f43])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    r1_tarski(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl5_2),
% 0.22/0.50    inference(resolution,[],[f59,f79])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    spl5_1 | spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f47,f78,f74])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ~spl5_1 | ~spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f48,f78,f74])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (606)------------------------------
% 0.22/0.50  % (606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (606)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (596)Refutation not found, incomplete strategy% (596)------------------------------
% 0.22/0.50  % (596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (596)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (596)Memory used [KB]: 10618
% 0.22/0.50  % (596)Time elapsed: 0.094 s
% 0.22/0.50  % (596)------------------------------
% 0.22/0.50  % (596)------------------------------
% 0.22/0.50  % (606)Memory used [KB]: 10746
% 0.22/0.50  % (606)Time elapsed: 0.089 s
% 0.22/0.50  % (606)------------------------------
% 0.22/0.50  % (606)------------------------------
% 0.22/0.51  % (595)Success in time 0.145 s
%------------------------------------------------------------------------------
