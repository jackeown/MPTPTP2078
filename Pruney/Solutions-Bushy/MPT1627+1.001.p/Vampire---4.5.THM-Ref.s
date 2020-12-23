%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1627+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:11 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 319 expanded)
%              Number of leaves         :    9 ( 122 expanded)
%              Depth                    :   25
%              Number of atoms          :  511 (3976 expanded)
%              Number of equality atoms :   51 ( 662 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f99,f186])).

fof(f186,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f184,f19])).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)
      | ~ r1_yellow_0(sK1,sK2) )
    & k1_xboole_0 != sK2
    & r1_yellow_0(sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & v1_waybel_0(sK2,sK1)
    & m1_yellow_0(sK1,sK0)
    & v4_waybel_0(sK1,sK0)
    & v4_yellow_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f13,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                  | ~ r1_yellow_0(X1,X2) )
                & k1_xboole_0 != X2
                & r1_yellow_0(X0,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v1_waybel_0(X2,X1) )
            & m1_yellow_0(X1,X0)
            & v4_waybel_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X1,X2) != k1_yellow_0(sK0,X2)
                | ~ r1_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r1_yellow_0(sK0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v1_waybel_0(X2,X1) )
          & m1_yellow_0(X1,sK0)
          & v4_waybel_0(X1,sK0)
          & v4_yellow_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k1_yellow_0(X1,X2) != k1_yellow_0(sK0,X2)
              | ~ r1_yellow_0(X1,X2) )
            & k1_xboole_0 != X2
            & r1_yellow_0(sK0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
            & v1_waybel_0(X2,X1) )
        & m1_yellow_0(X1,sK0)
        & v4_waybel_0(X1,sK0)
        & v4_yellow_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k1_yellow_0(sK0,X2) != k1_yellow_0(sK1,X2)
            | ~ r1_yellow_0(sK1,X2) )
          & k1_xboole_0 != X2
          & r1_yellow_0(sK0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
          & v1_waybel_0(X2,sK1) )
      & m1_yellow_0(sK1,sK0)
      & v4_waybel_0(sK1,sK0)
      & v4_yellow_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ( k1_yellow_0(sK0,X2) != k1_yellow_0(sK1,X2)
          | ~ r1_yellow_0(sK1,X2) )
        & k1_xboole_0 != X2
        & r1_yellow_0(sK0,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
        & v1_waybel_0(X2,sK1) )
   => ( ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)
        | ~ r1_yellow_0(sK1,sK2) )
      & k1_xboole_0 != sK2
      & r1_yellow_0(sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
      & v1_waybel_0(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r1_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v1_waybel_0(X2,X1) )
          & m1_yellow_0(X1,X0)
          & v4_waybel_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_yellow_0(X0,X2) != k1_yellow_0(X1,X2)
                | ~ r1_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r1_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v1_waybel_0(X2,X1) )
          & m1_yellow_0(X1,X0)
          & v4_waybel_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_waybel_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v1_waybel_0(X2,X1) )
               => ( r1_yellow_0(X0,X2)
                 => ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                      & r1_yellow_0(X1,X2) )
                    | k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_waybel_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v1_waybel_0(X2,X1) )
             => ( r1_yellow_0(X0,X2)
               => ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                    & r1_yellow_0(X1,X2) )
                  | k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_waybel_0)).

fof(f184,plain,
    ( v2_struct_0(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f183,f21])).

fof(f21,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f183,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f182,f25])).

fof(f25,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f182,plain,
    ( ~ m1_yellow_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f181,f24])).

fof(f24,plain,(
    v4_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f181,plain,
    ( ~ v4_waybel_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f180,f26])).

fof(f26,plain,(
    v1_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f180,plain,
    ( ~ v1_waybel_0(sK2,sK1)
    | ~ v4_waybel_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f179,f27])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f179,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v4_waybel_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f178,f28])).

fof(f28,plain,(
    r1_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f178,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v4_waybel_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f175,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f175,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_yellow_0(sK0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v1_waybel_0(sK2,sK1)
    | ~ v4_waybel_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_2 ),
    inference(resolution,[],[f149,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(k1_yellow_0(X0,X3),u1_struct_0(X1))
      | k1_xboole_0 = X3
      | ~ r1_yellow_0(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_waybel_0(X3,X1)
      | ~ v4_waybel_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_0(X1,X0)
              | ( ~ r2_hidden(k1_yellow_0(X0,sK3(X0,X1)),u1_struct_0(X1))
                & k1_xboole_0 != sK3(X0,X1)
                & r1_yellow_0(X0,sK3(X0,X1))
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
                & v1_waybel_0(sK3(X0,X1),X1) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),u1_struct_0(X1))
                  | k1_xboole_0 = X3
                  | ~ r1_yellow_0(X0,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v1_waybel_0(X3,X1) )
              | ~ v4_waybel_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
          & k1_xboole_0 != X2
          & r1_yellow_0(X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & v1_waybel_0(X2,X1) )
     => ( ~ r2_hidden(k1_yellow_0(X0,sK3(X0,X1)),u1_struct_0(X1))
        & k1_xboole_0 != sK3(X0,X1)
        & r1_yellow_0(X0,sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
        & v1_waybel_0(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & k1_xboole_0 != X2
                  & r1_yellow_0(X0,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v1_waybel_0(X2,X1) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),u1_struct_0(X1))
                  | k1_xboole_0 = X3
                  | ~ r1_yellow_0(X0,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v1_waybel_0(X3,X1) )
              | ~ v4_waybel_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_waybel_0(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & k1_xboole_0 != X2
                  & r1_yellow_0(X0,X2)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v1_waybel_0(X2,X1) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  | k1_xboole_0 = X2
                  | ~ r1_yellow_0(X0,X2)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  | ~ v1_waybel_0(X2,X1) )
              | ~ v4_waybel_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                | k1_xboole_0 = X2
                | ~ r1_yellow_0(X0,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v1_waybel_0(X2,X1) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                | k1_xboole_0 = X2
                | ~ r1_yellow_0(X0,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v1_waybel_0(X2,X1) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v1_waybel_0(X2,X1) )
               => ( r1_yellow_0(X0,X2)
                 => ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                    | k1_xboole_0 = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_waybel_0)).

fof(f149,plain,
    ( ~ r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | spl4_2 ),
    inference(subsumption_resolution,[],[f148,f19])).

fof(f148,plain,
    ( ~ r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f147,f20])).

fof(f20,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f147,plain,
    ( ~ r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f146,f21])).

fof(f146,plain,
    ( ~ r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f145,f23])).

fof(f23,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f145,plain,
    ( ~ r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ v4_yellow_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f144,f25])).

fof(f144,plain,
    ( ~ r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ m1_yellow_0(sK1,sK0)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f128,f28])).

fof(f128,plain,
    ( ~ r2_hidden(k1_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_yellow_0(sK0,sK2)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_2 ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,
    ( ! [X0] :
        ( k1_yellow_0(sK0,sK2) != k1_yellow_0(X0,sK2)
        | ~ r2_hidden(k1_yellow_0(X0,sK2),u1_struct_0(sK1))
        | ~ r1_yellow_0(X0,sK2)
        | ~ m1_yellow_0(sK1,X0)
        | ~ v4_yellow_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) )
    | spl4_2 ),
    inference(subsumption_resolution,[],[f110,f22])).

fof(f22,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f110,plain,
    ( ! [X0] :
        ( k1_yellow_0(sK0,sK2) != k1_yellow_0(X0,sK2)
        | ~ r2_hidden(k1_yellow_0(X0,sK2),u1_struct_0(sK1))
        | ~ r1_yellow_0(X0,sK2)
        | ~ m1_yellow_0(sK1,X0)
        | ~ v4_yellow_0(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) )
    | spl4_2 ),
    inference(subsumption_resolution,[],[f108,f27])).

fof(f108,plain,
    ( ! [X0] :
        ( k1_yellow_0(sK0,sK2) != k1_yellow_0(X0,sK2)
        | ~ r2_hidden(k1_yellow_0(X0,sK2),u1_struct_0(sK1))
        | ~ r1_yellow_0(X0,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_yellow_0(sK1,X0)
        | ~ v4_yellow_0(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0) )
    | spl4_2 ),
    inference(superposition,[],[f44,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
      | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                & r1_yellow_0(X1,X2) )
              | ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r1_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
                  & r1_yellow_0(X0,X2) )
               => ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
                  & r1_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_yellow_0)).

fof(f44,plain,
    ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_2
  <=> k1_yellow_0(sK0,sK2) = k1_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f99,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f97,f24])).

fof(f97,plain,
    ( ~ v4_waybel_0(sK1,sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f96,f19])).

fof(f96,plain,
    ( v2_struct_0(sK0)
    | ~ v4_waybel_0(sK1,sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f95,f20])).

fof(f95,plain,
    ( ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v4_waybel_0(sK1,sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f94,f21])).

fof(f94,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v4_waybel_0(sK1,sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f93,f28])).

fof(f93,plain,
    ( ~ r1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v4_waybel_0(sK1,sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f92,f25])).

fof(f92,plain,
    ( ~ m1_yellow_0(sK1,sK0)
    | ~ r1_yellow_0(sK0,sK2)
    | ~ l1_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v4_waybel_0(sK1,sK0)
    | spl4_1 ),
    inference(resolution,[],[f55,f23])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ v4_yellow_0(sK1,X0)
        | ~ m1_yellow_0(sK1,X0)
        | ~ r1_yellow_0(X0,sK2)
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ v4_waybel_0(sK1,X0) )
    | spl4_1 ),
    inference(subsumption_resolution,[],[f54,f26])).

fof(f54,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(X0,sK2)
        | ~ m1_yellow_0(sK1,X0)
        | ~ v4_yellow_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | ~ v1_waybel_0(sK2,sK1)
        | ~ v4_waybel_0(sK1,X0) )
    | spl4_1 ),
    inference(subsumption_resolution,[],[f53,f29])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(X0,sK2)
        | ~ m1_yellow_0(sK1,X0)
        | ~ v4_yellow_0(sK1,X0)
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | k1_xboole_0 = sK2
        | ~ v1_waybel_0(sK2,sK1)
        | ~ v4_waybel_0(sK1,X0) )
    | spl4_1 ),
    inference(subsumption_resolution,[],[f52,f22])).

fof(f52,plain,
    ( ! [X0] :
        ( ~ r1_yellow_0(X0,sK2)
        | ~ m1_yellow_0(sK1,X0)
        | ~ v4_yellow_0(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_orders_2(X0)
        | ~ v4_orders_2(X0)
        | v2_struct_0(X0)
        | k1_xboole_0 = sK2
        | ~ v1_waybel_0(sK2,sK1)
        | ~ v4_waybel_0(sK1,X0) )
    | spl4_1 ),
    inference(subsumption_resolution,[],[f50,f41])).

fof(f41,plain,
    ( ~ r1_yellow_0(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_1
  <=> r1_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r1_yellow_0(X0,sK2)
      | r1_yellow_0(sK1,sK2)
      | ~ m1_yellow_0(sK1,X0)
      | ~ v4_yellow_0(sK1,X0)
      | v2_struct_0(sK1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = sK2
      | ~ v1_waybel_0(sK2,sK1)
      | ~ v4_waybel_0(sK1,X0) ) ),
    inference(resolution,[],[f49,f27])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_yellow_0(X2,X1)
      | r1_yellow_0(X0,X1)
      | ~ m1_yellow_0(X0,X2)
      | ~ v4_yellow_0(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | k1_xboole_0 = X1
      | ~ v1_waybel_0(X1,X0)
      | ~ v4_waybel_0(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X0,X1)
      | ~ r1_yellow_0(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_yellow_0(X0,X2)
      | ~ v4_yellow_0(X0,X2)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X2)
      | ~ v4_orders_2(X2)
      | v2_struct_0(X2)
      | k1_xboole_0 = X1
      | ~ r1_yellow_0(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_waybel_0(X1,X0)
      | ~ v4_waybel_0(X0,X2)
      | ~ m1_yellow_0(X0,X2)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f31,f33])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k1_yellow_0(X0,X2),u1_struct_0(X1))
      | r1_yellow_0(X1,X2)
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_yellow_0(X1,X0)
      | ~ v4_yellow_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f45,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f30,f43,f40])).

fof(f30,plain,
    ( k1_yellow_0(sK0,sK2) != k1_yellow_0(sK1,sK2)
    | ~ r1_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
