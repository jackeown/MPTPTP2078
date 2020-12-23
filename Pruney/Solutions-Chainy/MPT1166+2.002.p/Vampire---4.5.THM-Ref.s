%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 259 expanded)
%              Number of leaves         :   10 ( 106 expanded)
%              Depth                    :   14
%              Number of atoms          :  290 (2209 expanded)
%              Number of equality atoms :   26 ( 265 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f148,f177])).

fof(f177,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f171])).

fof(f171,plain,
    ( $false
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f18,f19,f20,f21,f22,f51,f51,f26,f140,f24,f163,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_orders_2(X1)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ m1_orders_2(X4,X0,X2)
      | ~ sQ3_eqProxy(X4,X3)
      | sQ3_eqProxy(k1_xboole_0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ sQ3_eqProxy(X0,X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f50,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X1,X0,X1)
      | sQ3_eqProxy(k1_xboole_0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f28,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X1,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_orders_2(X1,X3,X5)
      | ~ sQ3_eqProxy(X2,X3)
      | ~ sQ3_eqProxy(X4,X5)
      | ~ m1_orders_2(X0,X2,X4)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f37])).

fof(f163,plain,
    ( ~ sQ3_eqProxy(k1_xboole_0,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f161,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f37])).

fof(f161,plain,
    ( ~ sQ3_eqProxy(sK2,k1_xboole_0)
    | ~ spl4_2 ),
    inference(resolution,[],[f140,f58])).

fof(f58,plain,(
    ! [X1] :
      ( ~ sQ3_eqProxy(sK1,X1)
      | ~ sQ3_eqProxy(X1,k1_xboole_0) ) ),
    inference(resolution,[],[f53,f54])).

fof(f54,plain,(
    ~ sQ3_eqProxy(sK1,k1_xboole_0) ),
    inference(resolution,[],[f52,f38])).

fof(f38,plain,(
    ~ sQ3_eqProxy(k1_xboole_0,sK1) ),
    inference(equality_proxy_replacement,[],[f25,f37])).

fof(f25,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( m1_orders_2(sK2,sK0,sK1)
    & m1_orders_2(sK1,sK0,sK2)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f14,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( m1_orders_2(X2,X0,X1)
                & m1_orders_2(X1,X0,X2)
                & k1_xboole_0 != X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,sK0,X1)
              & m1_orders_2(X1,sK0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( m1_orders_2(X2,sK0,X1)
            & m1_orders_2(X1,sK0,X2)
            & k1_xboole_0 != X1
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( m1_orders_2(X2,sK0,sK1)
          & m1_orders_2(sK1,sK0,X2)
          & k1_xboole_0 != sK1
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( m1_orders_2(X2,sK0,sK1)
        & m1_orders_2(sK1,sK0,X2)
        & k1_xboole_0 != sK1
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( m1_orders_2(sK2,sK0,sK1)
      & m1_orders_2(sK1,sK0,sK2)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sQ3_eqProxy(X0,X2)
      | ~ sQ3_eqProxy(X1,X2)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f37])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f140,plain,
    ( sQ3_eqProxy(sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl4_2
  <=> sQ3_eqProxy(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f26,plain,(
    m1_orders_2(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f37])).

fof(f22,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f19,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f18,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f148,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f18,f19,f20,f21,f22,f26,f24,f136,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f136,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f141,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f131,f138,f134])).

fof(f131,plain,
    ( sQ3_eqProxy(sK1,sK2)
    | ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f128,f27])).

fof(f27,plain,(
    m1_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f128,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK1)
      | sQ3_eqProxy(sK1,X0)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f112,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X1,sK0,X0)
      | sQ3_eqProxy(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f111,f18])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X1,sK0,X0)
      | v2_struct_0(sK0)
      | sQ3_eqProxy(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f110,f19])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | sQ3_eqProxy(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f109,f20])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | sQ3_eqProxy(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f107,f21])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_orders_2(X1,sK0,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | sQ3_eqProxy(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f86,f22])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_orders_2(X0,X1,X2)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | sQ3_eqProxy(X2,X0)
      | ~ r1_tarski(X2,X0) ) ),
    inference(resolution,[],[f30,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | sQ3_eqProxy(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f33,f37])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:49:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (2243)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.49  % (2235)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (2235)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f141,f148,f177])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    ~spl4_2),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f171])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    $false | ~spl4_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f18,f19,f20,f21,f22,f51,f51,f26,f140,f24,f163,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (~l1_orders_2(X1) | ~sQ3_eqProxy(X2,X3) | ~m1_orders_2(X4,X0,X2) | ~sQ3_eqProxy(X4,X3) | sQ3_eqProxy(k1_xboole_0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~sQ3_eqProxy(X0,X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.50    inference(resolution,[],[f50,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_orders_2(X1,X0,X1) | sQ3_eqProxy(k1_xboole_0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_proxy_replacement,[],[f28,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.50    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_orders_2(X1,X3,X5) | ~sQ3_eqProxy(X2,X3) | ~sQ3_eqProxy(X4,X5) | ~m1_orders_2(X0,X2,X4) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.50    inference(equality_proxy_axiom,[],[f37])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ~sQ3_eqProxy(k1_xboole_0,sK2) | ~spl4_2),
% 0.21/0.50    inference(resolution,[],[f161,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sQ3_eqProxy(X1,X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.50    inference(equality_proxy_axiom,[],[f37])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ~sQ3_eqProxy(sK2,k1_xboole_0) | ~spl4_2),
% 0.21/0.50    inference(resolution,[],[f140,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X1] : (~sQ3_eqProxy(sK1,X1) | ~sQ3_eqProxy(X1,k1_xboole_0)) )),
% 0.21/0.50    inference(resolution,[],[f53,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ~sQ3_eqProxy(sK1,k1_xboole_0)),
% 0.21/0.50    inference(resolution,[],[f52,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ~sQ3_eqProxy(k1_xboole_0,sK1)),
% 0.21/0.50    inference(equality_proxy_replacement,[],[f25,f37])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    k1_xboole_0 != sK1),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ((m1_orders_2(sK2,sK0,sK1) & m1_orders_2(sK1,sK0,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f14,f13,f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (m1_orders_2(X2,sK0,X1) & m1_orders_2(X1,sK0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (m1_orders_2(X2,sK0,X1) & m1_orders_2(X1,sK0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (m1_orders_2(X2,sK0,sK1) & m1_orders_2(sK1,sK0,X2) & k1_xboole_0 != sK1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X2] : (m1_orders_2(X2,sK0,sK1) & m1_orders_2(sK1,sK0,X2) & k1_xboole_0 != sK1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (m1_orders_2(sK2,sK0,sK1) & m1_orders_2(sK1,sK0,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f6])).
% 0.21/0.50  fof(f6,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f4])).
% 0.21/0.50  fof(f4,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sQ3_eqProxy(X0,X2) | ~sQ3_eqProxy(X1,X2) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.50    inference(equality_proxy_axiom,[],[f37])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    sQ3_eqProxy(sK1,sK2) | ~spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f138])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl4_2 <=> sQ3_eqProxy(sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    m1_orders_2(sK1,sK0,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0] : (sQ3_eqProxy(X0,X0)) )),
% 0.21/0.50    inference(equality_proxy_axiom,[],[f37])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    l1_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    v5_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    v4_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    v3_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    spl4_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f145])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    $false | spl4_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f18,f19,f20,f21,f22,f26,f24,f136,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    ~r1_tarski(sK1,sK2) | spl4_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f134])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    spl4_1 <=> r1_tarski(sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ~spl4_1 | spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f131,f138,f134])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    sQ3_eqProxy(sK1,sK2) | ~r1_tarski(sK1,sK2)),
% 0.21/0.50    inference(resolution,[],[f128,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    m1_orders_2(sK2,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_orders_2(X0,sK0,sK1) | sQ3_eqProxy(sK1,X0) | ~r1_tarski(sK1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f112,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | sQ3_eqProxy(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f111,f18])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | v2_struct_0(sK0) | sQ3_eqProxy(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f110,f19])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | sQ3_eqProxy(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f109,f20])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | sQ3_eqProxy(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f107,f21])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | sQ3_eqProxy(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f86,f22])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_orders_2(X0,X1,X2) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | sQ3_eqProxy(X2,X0) | ~r1_tarski(X2,X0)) )),
% 0.21/0.50    inference(resolution,[],[f30,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | sQ3_eqProxy(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(equality_proxy_replacement,[],[f33,f37])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (2235)------------------------------
% 0.21/0.50  % (2235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (2235)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (2235)Memory used [KB]: 6268
% 0.21/0.50  % (2235)Time elapsed: 0.071 s
% 0.21/0.50  % (2235)------------------------------
% 0.21/0.50  % (2235)------------------------------
% 0.21/0.51  % (2220)Success in time 0.141 s
%------------------------------------------------------------------------------
