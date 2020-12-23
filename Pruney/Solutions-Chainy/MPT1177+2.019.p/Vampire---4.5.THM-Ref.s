%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:20 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 823 expanded)
%              Number of leaves         :   24 ( 306 expanded)
%              Depth                    :   25
%              Number of atoms          :  735 (8095 expanded)
%              Number of equality atoms :   47 (  54 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f304,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f91,f167,f215,f219,f229,f234,f258,f303])).

fof(f303,plain,
    ( spl4_2
    | spl4_3
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl4_2
    | spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f301,f158])).

fof(f158,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl4_3
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f301,plain,
    ( r1_tarski(sK3,sK2)
    | spl4_2
    | spl4_4 ),
    inference(resolution,[],[f298,f148])).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f147,f54])).

fof(f54,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f40,f39,f38,f37])).

fof(f37,plain,
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

fof(f38,plain,
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

fof(f39,plain,
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

fof(f40,plain,
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0) ) ),
    inference(subsumption_resolution,[],[f146,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f145,f49])).

fof(f49,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f144,f50])).

fof(f50,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f143,f51])).

fof(f51,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f142,f52])).

fof(f52,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | ~ m1_orders_2(X1,sK0,X0)
      | r1_tarski(X1,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f141,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f141,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f140,f48])).

fof(f140,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f139,f49])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f138,f50])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f137,f51])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f136,f52])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f67,f53])).

fof(f53,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f298,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | spl4_2
    | spl4_4 ),
    inference(subsumption_resolution,[],[f297,f89])).

fof(f89,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_2
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f297,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f295,f161])).

fof(f161,plain,
    ( sK2 != sK3
    | spl4_4 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl4_4
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f295,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(resolution,[],[f292,f55])).

fof(f55,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f292,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | sK2 = X0
      | m1_orders_2(X0,sK0,sK2)
      | m1_orders_2(sK2,sK0,X0) ) ),
    inference(resolution,[],[f291,f54])).

fof(f291,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X1,sK0,sK1)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | m1_orders_2(X0,sK0,X1)
      | m1_orders_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f290,f48])).

fof(f290,plain,(
    ! [X0,X1] :
      ( m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | m1_orders_2(X1,sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f289,f49])).

fof(f289,plain,(
    ! [X0,X1] :
      ( m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | m1_orders_2(X1,sK0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f288,f50])).

fof(f288,plain,(
    ! [X0,X1] :
      ( m1_orders_2(X0,sK0,X1)
      | X0 = X1
      | ~ m2_orders_2(X0,sK0,sK1)
      | ~ m2_orders_2(X1,sK0,sK1)
      | m1_orders_2(X1,sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f287,f51])).

fof(f287,plain,(
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
    inference(subsumption_resolution,[],[f286,f52])).

fof(f286,plain,(
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
    inference(resolution,[],[f61,f53])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f258,plain,
    ( ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f249,f84])).

fof(f84,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_1
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f249,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f157,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f157,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f156])).

fof(f234,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f231,f209,f206])).

fof(f206,plain,
    ( spl4_5
  <=> ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK2)
        | ~ m1_orders_2(sK2,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f209,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f231,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | ~ m1_orders_2(X0,sK0,sK2)
      | ~ m1_orders_2(sK2,sK0,X0) ) ),
    inference(resolution,[],[f54,f203])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ m1_orders_2(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f202,f48])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X1,sK0,X0)
      | v2_struct_0(sK0)
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f201,f49])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f200,f50])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f199,f51])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f196,f52])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X0,sK0,X1)
      | k1_xboole_0 = X0
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m2_orders_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f182,f141])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X2,X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f63,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_2(X2,X0,X1)
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

fof(f229,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f224,f192])).

fof(f192,plain,(
    ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f191,f48])).

fof(f191,plain,
    ( v2_struct_0(sK0)
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f190,f49])).

fof(f190,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f189,f50])).

fof(f189,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f188,f51])).

fof(f188,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f187,f52])).

fof(f187,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m2_orders_2(k1_xboole_0,sK0,sK1) ),
    inference(resolution,[],[f185,f53])).

fof(f185,plain,(
    ! [X6,X5] :
      ( ~ m1_orders_1(X5,k1_orders_1(u1_struct_0(X6)))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | ~ v4_orders_2(X6)
      | ~ v3_orders_2(X6)
      | v2_struct_0(X6)
      | ~ m2_orders_2(k1_xboole_0,X6,X5) ) ),
    inference(resolution,[],[f181,f101])).

fof(f101,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(trivial_inequality_removal,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f75,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f94,f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f94,plain,(
    ! [X2,X1] : ~ r2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(resolution,[],[f78,f65])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_funct_1(X2,u1_struct_0(X1)))
      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m2_orders_2(X0,X1,X2) ) ),
    inference(resolution,[],[f59,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

fof(f224,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f54,f211])).

fof(f211,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f209])).

fof(f219,plain,
    ( ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f217,f64])).

fof(f64,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : ~ r2_xboole_0(X0,X0) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).

fof(f217,plain,
    ( r2_xboole_0(sK2,sK2)
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f84,f162])).

fof(f162,plain,
    ( sK2 = sK3
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f160])).

fof(f215,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f213,f170])).

fof(f170,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f88,f162])).

fof(f88,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f213,plain,
    ( ~ m1_orders_2(sK2,sK0,sK2)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f207,f170])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(sK2,sK0,X0)
        | ~ m1_orders_2(X0,sK0,sK2) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f206])).

fof(f167,plain,
    ( spl4_4
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f154,f87,f83,f160])).

fof(f154,plain,
    ( sK2 = sK3
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f151,f85])).

fof(f85,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f151,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK2,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f150,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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

fof(f150,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f149,f88])).

fof(f149,plain,(
    ! [X1] :
      ( ~ m1_orders_2(X1,sK0,sK3)
      | r1_tarski(X1,sK3) ) ),
    inference(resolution,[],[f147,f55])).

fof(f91,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f56,f87,f83])).

fof(f56,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f57,f87,f83])).

fof(f57,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:25:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (14598)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.49  % (14598)Refutation not found, incomplete strategy% (14598)------------------------------
% 0.22/0.49  % (14598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (14598)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (14598)Memory used [KB]: 6140
% 0.22/0.49  % (14598)Time elapsed: 0.079 s
% 0.22/0.49  % (14598)------------------------------
% 0.22/0.49  % (14598)------------------------------
% 0.22/0.50  % (14600)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (14617)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (14597)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (14606)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (14594)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (14606)Refutation not found, incomplete strategy% (14606)------------------------------
% 0.22/0.51  % (14606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (14606)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (14606)Memory used [KB]: 6140
% 0.22/0.51  % (14606)Time elapsed: 0.097 s
% 0.22/0.51  % (14606)------------------------------
% 0.22/0.51  % (14606)------------------------------
% 0.22/0.51  % (14596)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (14611)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (14599)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (14599)Refutation not found, incomplete strategy% (14599)------------------------------
% 0.22/0.52  % (14599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14599)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (14599)Memory used [KB]: 10618
% 0.22/0.52  % (14599)Time elapsed: 0.101 s
% 0.22/0.52  % (14599)------------------------------
% 0.22/0.52  % (14599)------------------------------
% 0.22/0.52  % (14595)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (14610)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (14607)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.30/0.53  % (14604)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.30/0.53  % (14603)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.30/0.53  % (14613)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.30/0.53  % (14604)Refutation not found, incomplete strategy% (14604)------------------------------
% 1.30/0.53  % (14604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (14604)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (14604)Memory used [KB]: 10618
% 1.30/0.53  % (14604)Time elapsed: 0.117 s
% 1.30/0.53  % (14604)------------------------------
% 1.30/0.53  % (14604)------------------------------
% 1.30/0.53  % (14593)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.30/0.53  % (14593)Refutation not found, incomplete strategy% (14593)------------------------------
% 1.30/0.53  % (14593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (14593)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (14593)Memory used [KB]: 10618
% 1.30/0.53  % (14593)Time elapsed: 0.112 s
% 1.30/0.53  % (14593)------------------------------
% 1.30/0.53  % (14593)------------------------------
% 1.30/0.53  % (14594)Refutation not found, incomplete strategy% (14594)------------------------------
% 1.30/0.53  % (14594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (14594)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (14594)Memory used [KB]: 10746
% 1.30/0.53  % (14594)Time elapsed: 0.106 s
% 1.30/0.53  % (14594)------------------------------
% 1.30/0.53  % (14594)------------------------------
% 1.30/0.53  % (14605)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.30/0.53  % (14618)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.30/0.53  % (14597)Refutation found. Thanks to Tanya!
% 1.30/0.53  % SZS status Theorem for theBenchmark
% 1.30/0.53  % SZS output start Proof for theBenchmark
% 1.30/0.53  fof(f304,plain,(
% 1.30/0.53    $false),
% 1.30/0.53    inference(avatar_sat_refutation,[],[f90,f91,f167,f215,f219,f229,f234,f258,f303])).
% 1.30/0.53  fof(f303,plain,(
% 1.30/0.53    spl4_2 | spl4_3 | spl4_4),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f302])).
% 1.30/0.53  fof(f302,plain,(
% 1.30/0.53    $false | (spl4_2 | spl4_3 | spl4_4)),
% 1.30/0.53    inference(subsumption_resolution,[],[f301,f158])).
% 1.30/0.53  fof(f158,plain,(
% 1.30/0.53    ~r1_tarski(sK3,sK2) | spl4_3),
% 1.30/0.53    inference(avatar_component_clause,[],[f156])).
% 1.30/0.53  fof(f156,plain,(
% 1.30/0.53    spl4_3 <=> r1_tarski(sK3,sK2)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.30/0.53  fof(f301,plain,(
% 1.30/0.53    r1_tarski(sK3,sK2) | (spl4_2 | spl4_4)),
% 1.30/0.53    inference(resolution,[],[f298,f148])).
% 1.30/0.53  fof(f148,plain,(
% 1.30/0.53    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | r1_tarski(X0,sK2)) )),
% 1.30/0.53    inference(resolution,[],[f147,f54])).
% 1.30/0.53  fof(f54,plain,(
% 1.30/0.53    m2_orders_2(sK2,sK0,sK1)),
% 1.30/0.53    inference(cnf_transformation,[],[f41])).
% 1.30/0.53  fof(f41,plain,(
% 1.30/0.53    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f40,f39,f38,f37])).
% 1.30/0.53  fof(f37,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f38,plain,(
% 1.30/0.53    ? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f39,plain,(
% 1.30/0.53    ? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f40,plain,(
% 1.30/0.53    ? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) => ((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f36,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.30/0.53    inference(flattening,[],[f35])).
% 1.30/0.53  fof(f35,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.30/0.53    inference(nnf_transformation,[],[f19])).
% 1.30/0.53  fof(f19,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.30/0.53    inference(flattening,[],[f18])).
% 1.30/0.53  fof(f18,plain,(
% 1.30/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.30/0.53    inference(ennf_transformation,[],[f16])).
% 1.30/0.53  fof(f16,negated_conjecture,(
% 1.30/0.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.30/0.53    inference(negated_conjecture,[],[f15])).
% 1.30/0.53  fof(f15,conjecture,(
% 1.30/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.30/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).
% 1.30/0.54  fof(f147,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f146,f48])).
% 1.30/0.54  fof(f48,plain,(
% 1.30/0.54    ~v2_struct_0(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f41])).
% 1.30/0.54  fof(f146,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f145,f49])).
% 1.30/0.54  fof(f49,plain,(
% 1.30/0.54    v3_orders_2(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f41])).
% 1.30/0.54  fof(f145,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f144,f50])).
% 1.30/0.54  fof(f50,plain,(
% 1.30/0.54    v4_orders_2(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f41])).
% 1.30/0.54  fof(f144,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f143,f51])).
% 1.30/0.54  fof(f51,plain,(
% 1.30/0.54    v5_orders_2(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f41])).
% 1.30/0.54  fof(f143,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f142,f52])).
% 1.30/0.54  fof(f52,plain,(
% 1.30/0.54    l1_orders_2(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f41])).
% 1.30/0.54  fof(f142,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | ~m1_orders_2(X1,sK0,X0) | r1_tarski(X1,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(resolution,[],[f141,f62])).
% 1.30/0.54  fof(f62,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f26])).
% 1.30/0.54  fof(f26,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f25])).
% 1.30/0.54  fof(f25,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f11])).
% 1.30/0.54  fof(f11,axiom,(
% 1.30/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).
% 1.30/0.54  fof(f141,plain,(
% 1.30/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,sK1)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f140,f48])).
% 1.30/0.54  fof(f140,plain,(
% 1.30/0.54    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f139,f49])).
% 1.30/0.54  fof(f139,plain,(
% 1.30/0.54    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f138,f50])).
% 1.30/0.54  fof(f138,plain,(
% 1.30/0.54    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f137,f51])).
% 1.30/0.54  fof(f137,plain,(
% 1.30/0.54    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f136,f52])).
% 1.30/0.54  fof(f136,plain,(
% 1.30/0.54    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(resolution,[],[f67,f53])).
% 1.30/0.54  fof(f53,plain,(
% 1.30/0.54    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 1.30/0.54    inference(cnf_transformation,[],[f41])).
% 1.30/0.54  fof(f67,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f30])).
% 1.30/0.54  fof(f30,plain,(
% 1.30/0.54    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f29])).
% 1.30/0.54  fof(f29,plain,(
% 1.30/0.54    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f10])).
% 1.30/0.54  fof(f10,axiom,(
% 1.30/0.54    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 1.30/0.54  fof(f298,plain,(
% 1.30/0.54    m1_orders_2(sK3,sK0,sK2) | (spl4_2 | spl4_4)),
% 1.30/0.54    inference(subsumption_resolution,[],[f297,f89])).
% 1.30/0.54  fof(f89,plain,(
% 1.30/0.54    ~m1_orders_2(sK2,sK0,sK3) | spl4_2),
% 1.30/0.54    inference(avatar_component_clause,[],[f87])).
% 1.30/0.54  fof(f87,plain,(
% 1.30/0.54    spl4_2 <=> m1_orders_2(sK2,sK0,sK3)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.30/0.54  fof(f297,plain,(
% 1.30/0.54    m1_orders_2(sK3,sK0,sK2) | m1_orders_2(sK2,sK0,sK3) | spl4_4),
% 1.30/0.54    inference(subsumption_resolution,[],[f295,f161])).
% 1.30/0.54  fof(f161,plain,(
% 1.30/0.54    sK2 != sK3 | spl4_4),
% 1.30/0.54    inference(avatar_component_clause,[],[f160])).
% 1.30/0.54  fof(f160,plain,(
% 1.30/0.54    spl4_4 <=> sK2 = sK3),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.30/0.54  fof(f295,plain,(
% 1.30/0.54    sK2 = sK3 | m1_orders_2(sK3,sK0,sK2) | m1_orders_2(sK2,sK0,sK3)),
% 1.30/0.54    inference(resolution,[],[f292,f55])).
% 1.30/0.54  fof(f55,plain,(
% 1.30/0.54    m2_orders_2(sK3,sK0,sK1)),
% 1.30/0.54    inference(cnf_transformation,[],[f41])).
% 1.30/0.54  fof(f292,plain,(
% 1.30/0.54    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK2 = X0 | m1_orders_2(X0,sK0,sK2) | m1_orders_2(sK2,sK0,X0)) )),
% 1.30/0.54    inference(resolution,[],[f291,f54])).
% 1.30/0.54  fof(f291,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f290,f48])).
% 1.30/0.54  fof(f290,plain,(
% 1.30/0.54    ( ! [X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X1,sK0,X0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f289,f49])).
% 1.30/0.54  fof(f289,plain,(
% 1.30/0.54    ( ! [X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X1,sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f288,f50])).
% 1.30/0.54  fof(f288,plain,(
% 1.30/0.54    ( ! [X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X1,sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f287,f51])).
% 1.30/0.54  fof(f287,plain,(
% 1.30/0.54    ( ! [X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X1,sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f286,f52])).
% 1.30/0.54  fof(f286,plain,(
% 1.30/0.54    ( ! [X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,sK1) | ~m2_orders_2(X1,sK0,sK1) | m1_orders_2(X1,sK0,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.30/0.54    inference(resolution,[],[f61,f53])).
% 1.30/0.54  fof(f61,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | m1_orders_2(X2,X0,X3) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f42])).
% 1.30/0.54  fof(f42,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(nnf_transformation,[],[f24])).
% 1.30/0.54  fof(f24,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f23])).
% 1.30/0.54  fof(f23,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f14])).
% 1.30/0.54  fof(f14,axiom,(
% 1.30/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).
% 1.30/0.54  fof(f258,plain,(
% 1.30/0.54    ~spl4_1 | ~spl4_3),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f257])).
% 1.30/0.54  fof(f257,plain,(
% 1.30/0.54    $false | (~spl4_1 | ~spl4_3)),
% 1.30/0.54    inference(subsumption_resolution,[],[f249,f84])).
% 1.30/0.54  fof(f84,plain,(
% 1.30/0.54    r2_xboole_0(sK2,sK3) | ~spl4_1),
% 1.30/0.54    inference(avatar_component_clause,[],[f83])).
% 1.30/0.54  fof(f83,plain,(
% 1.30/0.54    spl4_1 <=> r2_xboole_0(sK2,sK3)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.30/0.54  fof(f249,plain,(
% 1.30/0.54    ~r2_xboole_0(sK2,sK3) | ~spl4_3),
% 1.30/0.54    inference(resolution,[],[f157,f78])).
% 1.30/0.54  fof(f78,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f34])).
% 1.30/0.54  fof(f34,plain,(
% 1.30/0.54    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 1.30/0.54    inference(ennf_transformation,[],[f6])).
% 1.30/0.54  fof(f6,axiom,(
% 1.30/0.54    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 1.30/0.54  fof(f157,plain,(
% 1.30/0.54    r1_tarski(sK3,sK2) | ~spl4_3),
% 1.30/0.54    inference(avatar_component_clause,[],[f156])).
% 1.30/0.54  fof(f234,plain,(
% 1.30/0.54    spl4_5 | spl4_6),
% 1.30/0.54    inference(avatar_split_clause,[],[f231,f209,f206])).
% 1.30/0.54  fof(f206,plain,(
% 1.30/0.54    spl4_5 <=> ! [X0] : (~m1_orders_2(X0,sK0,sK2) | ~m1_orders_2(sK2,sK0,X0))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.30/0.54  fof(f209,plain,(
% 1.30/0.54    spl4_6 <=> k1_xboole_0 = sK2),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.30/0.54  fof(f231,plain,(
% 1.30/0.54    ( ! [X0] : (k1_xboole_0 = sK2 | ~m1_orders_2(X0,sK0,sK2) | ~m1_orders_2(sK2,sK0,X0)) )),
% 1.30/0.54    inference(resolution,[],[f54,f203])).
% 1.30/0.54  fof(f203,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | k1_xboole_0 = X0 | ~m1_orders_2(X1,sK0,X0) | ~m1_orders_2(X0,sK0,X1)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f202,f48])).
% 1.30/0.54  fof(f202,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_orders_2(X1,sK0,X0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f201,f49])).
% 1.30/0.54  fof(f201,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_orders_2(X1,sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f200,f50])).
% 1.30/0.54  fof(f200,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_orders_2(X1,sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f199,f51])).
% 1.30/0.54  fof(f199,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_orders_2(X1,sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f196,f52])).
% 1.30/0.54  fof(f196,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X0 | ~m1_orders_2(X1,sK0,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(X0,sK0,sK1)) )),
% 1.30/0.54    inference(resolution,[],[f182,f141])).
% 1.30/0.54  fof(f182,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_orders_2(X2,X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f63,f68])).
% 1.30/0.54  fof(f68,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f32])).
% 1.30/0.54  fof(f32,plain,(
% 1.30/0.54    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f31])).
% 1.30/0.54  fof(f31,plain,(
% 1.30/0.54    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f9])).
% 1.30/0.54  fof(f9,axiom,(
% 1.30/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 1.30/0.54  fof(f63,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f28])).
% 1.30/0.54  fof(f28,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f27])).
% 1.30/0.54  fof(f27,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f12])).
% 1.30/0.54  fof(f12,axiom,(
% 1.30/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).
% 1.30/0.54  fof(f229,plain,(
% 1.30/0.54    ~spl4_6),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f228])).
% 1.30/0.54  fof(f228,plain,(
% 1.30/0.54    $false | ~spl4_6),
% 1.30/0.54    inference(subsumption_resolution,[],[f224,f192])).
% 1.30/0.54  fof(f192,plain,(
% 1.30/0.54    ~m2_orders_2(k1_xboole_0,sK0,sK1)),
% 1.30/0.54    inference(subsumption_resolution,[],[f191,f48])).
% 1.30/0.54  fof(f191,plain,(
% 1.30/0.54    v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,sK1)),
% 1.30/0.54    inference(subsumption_resolution,[],[f190,f49])).
% 1.30/0.54  fof(f190,plain,(
% 1.30/0.54    ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,sK1)),
% 1.30/0.54    inference(subsumption_resolution,[],[f189,f50])).
% 1.30/0.54  fof(f189,plain,(
% 1.30/0.54    ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,sK1)),
% 1.30/0.54    inference(subsumption_resolution,[],[f188,f51])).
% 1.30/0.54  fof(f188,plain,(
% 1.30/0.54    ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,sK1)),
% 1.30/0.54    inference(subsumption_resolution,[],[f187,f52])).
% 1.30/0.54  fof(f187,plain,(
% 1.30/0.54    ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m2_orders_2(k1_xboole_0,sK0,sK1)),
% 1.30/0.54    inference(resolution,[],[f185,f53])).
% 1.30/0.54  fof(f185,plain,(
% 1.30/0.54    ( ! [X6,X5] : (~m1_orders_1(X5,k1_orders_1(u1_struct_0(X6))) | ~l1_orders_2(X6) | ~v5_orders_2(X6) | ~v4_orders_2(X6) | ~v3_orders_2(X6) | v2_struct_0(X6) | ~m2_orders_2(k1_xboole_0,X6,X5)) )),
% 1.30/0.54    inference(resolution,[],[f181,f101])).
% 1.30/0.54  fof(f101,plain,(
% 1.30/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.30/0.54    inference(trivial_inequality_removal,[],[f100])).
% 1.30/0.54  fof(f100,plain,(
% 1.30/0.54    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_xboole_0,X0)) )),
% 1.30/0.54    inference(superposition,[],[f75,f96])).
% 1.30/0.54  fof(f96,plain,(
% 1.30/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.30/0.54    inference(resolution,[],[f94,f58])).
% 1.30/0.54  fof(f58,plain,(
% 1.30/0.54    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 1.30/0.54    inference(cnf_transformation,[],[f20])).
% 1.30/0.54  fof(f20,plain,(
% 1.30/0.54    ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 1.30/0.54    inference(ennf_transformation,[],[f7])).
% 1.30/0.54  fof(f7,axiom,(
% 1.30/0.54    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).
% 1.30/0.54  fof(f94,plain,(
% 1.30/0.54    ( ! [X2,X1] : (~r2_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 1.30/0.54    inference(resolution,[],[f78,f65])).
% 1.30/0.54  fof(f65,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f5])).
% 1.30/0.54  fof(f5,axiom,(
% 1.30/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.30/0.54  fof(f75,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f47])).
% 1.30/0.54  fof(f47,plain,(
% 1.30/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.30/0.54    inference(nnf_transformation,[],[f4])).
% 1.30/0.54  fof(f4,axiom,(
% 1.30/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.30/0.54  fof(f181,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_funct_1(X2,u1_struct_0(X1))) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | ~m2_orders_2(X0,X1,X2)) )),
% 1.30/0.54    inference(resolution,[],[f59,f77])).
% 1.30/0.54  fof(f77,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f33])).
% 1.30/0.54  fof(f33,plain,(
% 1.30/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.30/0.54    inference(ennf_transformation,[],[f8])).
% 1.30/0.54  fof(f8,axiom,(
% 1.30/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.30/0.54  fof(f59,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f22])).
% 1.30/0.54  fof(f22,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.30/0.54    inference(flattening,[],[f21])).
% 1.30/0.54  fof(f21,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f13])).
% 1.30/0.54  fof(f13,axiom,(
% 1.30/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).
% 1.30/0.54  fof(f224,plain,(
% 1.30/0.54    m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl4_6),
% 1.30/0.54    inference(backward_demodulation,[],[f54,f211])).
% 1.30/0.54  fof(f211,plain,(
% 1.30/0.54    k1_xboole_0 = sK2 | ~spl4_6),
% 1.30/0.54    inference(avatar_component_clause,[],[f209])).
% 1.30/0.54  fof(f219,plain,(
% 1.30/0.54    ~spl4_1 | ~spl4_4),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f218])).
% 1.30/0.54  fof(f218,plain,(
% 1.30/0.54    $false | (~spl4_1 | ~spl4_4)),
% 1.30/0.54    inference(subsumption_resolution,[],[f217,f64])).
% 1.30/0.54  fof(f64,plain,(
% 1.30/0.54    ( ! [X0] : (~r2_xboole_0(X0,X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f17])).
% 1.30/0.54  fof(f17,plain,(
% 1.30/0.54    ! [X0] : ~r2_xboole_0(X0,X0)),
% 1.30/0.54    inference(rectify,[],[f2])).
% 1.30/0.54  fof(f2,axiom,(
% 1.30/0.54    ! [X0,X1] : ~r2_xboole_0(X0,X0)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_xboole_0)).
% 1.30/0.54  fof(f217,plain,(
% 1.30/0.54    r2_xboole_0(sK2,sK2) | (~spl4_1 | ~spl4_4)),
% 1.30/0.54    inference(forward_demodulation,[],[f84,f162])).
% 1.30/0.54  fof(f162,plain,(
% 1.30/0.54    sK2 = sK3 | ~spl4_4),
% 1.30/0.54    inference(avatar_component_clause,[],[f160])).
% 1.30/0.54  fof(f215,plain,(
% 1.30/0.54    ~spl4_2 | ~spl4_4 | ~spl4_5),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f214])).
% 1.30/0.54  fof(f214,plain,(
% 1.30/0.54    $false | (~spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.30/0.54    inference(subsumption_resolution,[],[f213,f170])).
% 1.30/0.54  fof(f170,plain,(
% 1.30/0.54    m1_orders_2(sK2,sK0,sK2) | (~spl4_2 | ~spl4_4)),
% 1.30/0.54    inference(backward_demodulation,[],[f88,f162])).
% 1.30/0.54  fof(f88,plain,(
% 1.30/0.54    m1_orders_2(sK2,sK0,sK3) | ~spl4_2),
% 1.30/0.54    inference(avatar_component_clause,[],[f87])).
% 1.30/0.54  fof(f213,plain,(
% 1.30/0.54    ~m1_orders_2(sK2,sK0,sK2) | (~spl4_2 | ~spl4_4 | ~spl4_5)),
% 1.30/0.54    inference(resolution,[],[f207,f170])).
% 1.30/0.54  fof(f207,plain,(
% 1.30/0.54    ( ! [X0] : (~m1_orders_2(sK2,sK0,X0) | ~m1_orders_2(X0,sK0,sK2)) ) | ~spl4_5),
% 1.30/0.54    inference(avatar_component_clause,[],[f206])).
% 1.30/0.54  fof(f167,plain,(
% 1.30/0.54    spl4_4 | spl4_1 | ~spl4_2),
% 1.30/0.54    inference(avatar_split_clause,[],[f154,f87,f83,f160])).
% 1.30/0.54  fof(f154,plain,(
% 1.30/0.54    sK2 = sK3 | (spl4_1 | ~spl4_2)),
% 1.30/0.54    inference(subsumption_resolution,[],[f151,f85])).
% 1.30/0.54  fof(f85,plain,(
% 1.30/0.54    ~r2_xboole_0(sK2,sK3) | spl4_1),
% 1.30/0.54    inference(avatar_component_clause,[],[f83])).
% 1.30/0.54  fof(f151,plain,(
% 1.30/0.54    sK2 = sK3 | r2_xboole_0(sK2,sK3) | ~spl4_2),
% 1.30/0.54    inference(resolution,[],[f150,f74])).
% 1.30/0.54  fof(f74,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f46])).
% 1.30/0.54  fof(f46,plain,(
% 1.30/0.54    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.30/0.54    inference(flattening,[],[f45])).
% 1.30/0.54  fof(f45,plain,(
% 1.30/0.54    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 1.30/0.54    inference(nnf_transformation,[],[f1])).
% 1.30/0.54  fof(f1,axiom,(
% 1.30/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.30/0.54  fof(f150,plain,(
% 1.30/0.54    r1_tarski(sK2,sK3) | ~spl4_2),
% 1.30/0.54    inference(resolution,[],[f149,f88])).
% 1.30/0.54  fof(f149,plain,(
% 1.30/0.54    ( ! [X1] : (~m1_orders_2(X1,sK0,sK3) | r1_tarski(X1,sK3)) )),
% 1.30/0.54    inference(resolution,[],[f147,f55])).
% 1.30/0.54  fof(f91,plain,(
% 1.30/0.54    spl4_1 | spl4_2),
% 1.30/0.54    inference(avatar_split_clause,[],[f56,f87,f83])).
% 1.30/0.54  fof(f56,plain,(
% 1.30/0.54    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 1.30/0.54    inference(cnf_transformation,[],[f41])).
% 1.30/0.54  fof(f90,plain,(
% 1.30/0.54    ~spl4_1 | ~spl4_2),
% 1.30/0.54    inference(avatar_split_clause,[],[f57,f87,f83])).
% 1.30/0.54  fof(f57,plain,(
% 1.30/0.54    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 1.30/0.54    inference(cnf_transformation,[],[f41])).
% 1.30/0.54  % SZS output end Proof for theBenchmark
% 1.30/0.54  % (14597)------------------------------
% 1.30/0.54  % (14597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (14597)Termination reason: Refutation
% 1.30/0.54  
% 1.30/0.54  % (14597)Memory used [KB]: 6268
% 1.30/0.54  % (14597)Time elapsed: 0.125 s
% 1.30/0.54  % (14597)------------------------------
% 1.30/0.54  % (14597)------------------------------
% 1.30/0.54  % (14592)Success in time 0.174 s
%------------------------------------------------------------------------------
