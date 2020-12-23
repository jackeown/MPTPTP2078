%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 419 expanded)
%              Number of leaves         :   17 ( 144 expanded)
%              Depth                    :   25
%              Number of atoms          :  679 (4046 expanded)
%              Number of equality atoms :   55 ( 110 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (12787)Refutation not found, incomplete strategy% (12787)------------------------------
% (12787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12787)Termination reason: Refutation not found, incomplete strategy

% (12787)Memory used [KB]: 10618
% (12787)Time elapsed: 0.089 s
% (12787)------------------------------
% (12787)------------------------------
fof(f436,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f412,f421,f428,f435])).

fof(f435,plain,(
    ~ spl8_1 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f433,f65])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( ~ l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0)
      | ~ v7_waybel_0(k3_waybel_2(sK0,sK1,sK2))
      | ~ v4_orders_2(k3_waybel_2(sK0,sK1,sK2))
      | v2_struct_0(k3_waybel_2(sK0,sK1,sK2)) )
    & l1_waybel_0(sK2,sK0)
    & v7_waybel_0(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
                  | ~ v7_waybel_0(k3_waybel_2(X0,X1,X2))
                  | ~ v4_orders_2(k3_waybel_2(X0,X1,X2))
                  | v2_struct_0(k3_waybel_2(X0,X1,X2)) )
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ l1_waybel_0(k3_waybel_2(sK0,X1,X2),sK0)
                | ~ v7_waybel_0(k3_waybel_2(sK0,X1,X2))
                | ~ v4_orders_2(k3_waybel_2(sK0,X1,X2))
                | v2_struct_0(k3_waybel_2(sK0,X1,X2)) )
              & l1_waybel_0(X2,sK0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ l1_waybel_0(k3_waybel_2(sK0,X1,X2),sK0)
              | ~ v7_waybel_0(k3_waybel_2(sK0,X1,X2))
              | ~ v4_orders_2(k3_waybel_2(sK0,X1,X2))
              | v2_struct_0(k3_waybel_2(sK0,X1,X2)) )
            & l1_waybel_0(X2,sK0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ l1_waybel_0(k3_waybel_2(sK0,sK1,X2),sK0)
            | ~ v7_waybel_0(k3_waybel_2(sK0,sK1,X2))
            | ~ v4_orders_2(k3_waybel_2(sK0,sK1,X2))
            | v2_struct_0(k3_waybel_2(sK0,sK1,X2)) )
          & l1_waybel_0(X2,sK0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ( ~ l1_waybel_0(k3_waybel_2(sK0,sK1,X2),sK0)
          | ~ v7_waybel_0(k3_waybel_2(sK0,sK1,X2))
          | ~ v4_orders_2(k3_waybel_2(sK0,sK1,X2))
          | v2_struct_0(k3_waybel_2(sK0,sK1,X2)) )
        & l1_waybel_0(X2,sK0)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
   => ( ( ~ l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0)
        | ~ v7_waybel_0(k3_waybel_2(sK0,sK1,sK2))
        | ~ v4_orders_2(k3_waybel_2(sK0,sK1,sK2))
        | v2_struct_0(k3_waybel_2(sK0,sK1,sK2)) )
      & l1_waybel_0(sK2,sK0)
      & v7_waybel_0(sK2)
      & v4_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
                | ~ v7_waybel_0(k3_waybel_2(X0,X1,X2))
                | ~ v4_orders_2(k3_waybel_2(X0,X1,X2))
                | v2_struct_0(k3_waybel_2(X0,X1,X2)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
                | ~ v7_waybel_0(k3_waybel_2(X0,X1,X2))
                | ~ v4_orders_2(k3_waybel_2(X0,X1,X2))
                | v2_struct_0(k3_waybel_2(X0,X1,X2)) )
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
                  & v7_waybel_0(k3_waybel_2(X0,X1,X2))
                  & v4_orders_2(k3_waybel_2(X0,X1,X2))
                  & ~ v2_struct_0(k3_waybel_2(X0,X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
                & v7_waybel_0(k3_waybel_2(X0,X1,X2))
                & v4_orders_2(k3_waybel_2(X0,X1,X2))
                & ~ v2_struct_0(k3_waybel_2(X0,X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_9)).

fof(f433,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f432,f66])).

fof(f66,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f432,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f431,f67])).

fof(f67,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f431,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f430,f68])).

fof(f68,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f430,plain,
    ( v2_struct_0(sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f429,f71])).

fof(f71,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f429,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_1 ),
    inference(resolution,[],[f114,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k3_waybel_2(X0,X1,X2))
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_waybel_2(X0,X1,X2)) )
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_waybel_2(X0,X1,X2)) )
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_waybel_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_waybel_2)).

fof(f114,plain,
    ( v2_struct_0(k3_waybel_2(sK0,sK1,sK2))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl8_1
  <=> v2_struct_0(k3_waybel_2(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f428,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | spl8_4 ),
    inference(subsumption_resolution,[],[f426,f65])).

fof(f426,plain,
    ( v2_struct_0(sK0)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f425,f66])).

fof(f425,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f424,f67])).

fof(f424,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f423,f68])).

fof(f423,plain,
    ( v2_struct_0(sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_4 ),
    inference(subsumption_resolution,[],[f422,f71])).

fof(f422,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_4 ),
    inference(resolution,[],[f123,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) )
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) )
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
        & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_waybel_2)).

fof(f123,plain,
    ( ~ l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_4
  <=> l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f421,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f419,f127])).

fof(f127,plain,(
    l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f126,f125])).

fof(f125,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f74,f66])).

fof(f74,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f126,plain,
    ( l1_orders_2(sK2)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f73,f71])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | l1_orders_2(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f419,plain,
    ( ~ l1_orders_2(sK2)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f418,f70])).

fof(f70,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f418,plain,
    ( ~ v7_waybel_0(sK2)
    | ~ l1_orders_2(sK2)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f417,f65])).

fof(f417,plain,
    ( v2_struct_0(sK0)
    | ~ v7_waybel_0(sK2)
    | ~ l1_orders_2(sK2)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f416,f66])).

fof(f416,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v7_waybel_0(sK2)
    | ~ l1_orders_2(sK2)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f415,f67])).

fof(f415,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v7_waybel_0(sK2)
    | ~ l1_orders_2(sK2)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f414,f68])).

fof(f414,plain,
    ( v2_struct_0(sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v7_waybel_0(sK2)
    | ~ l1_orders_2(sK2)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f413,f71])).

fof(f413,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v7_waybel_0(sK2)
    | ~ l1_orders_2(sK2)
    | spl8_3 ),
    inference(resolution,[],[f120,f270])).

fof(f270,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_waybel_2(X0,X1,X2))
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v7_waybel_0(X2)
      | ~ l1_orders_2(X2) ) ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_waybel_2(X0,X1,X2))
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v7_waybel_0(X2)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f190,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v7_waybel_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ~ v7_waybel_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) )
        & ( v7_waybel_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v7_waybel_0(X0)
      <=> v7_waybel_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v7_waybel_0(X0)
      <=> v7_waybel_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(X0)
      <=> v7_waybel_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l15_yellow_6)).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))
      | v7_waybel_0(k3_waybel_2(X0,X1,X2))
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f189,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))
      | v7_waybel_0(k3_waybel_2(X0,X1,X2))
      | ~ v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f188,f102])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))
      | v7_waybel_0(k3_waybel_2(X0,X1,X2))
      | ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f187,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( l1_orders_2(k3_waybel_2(X1,X2,X0))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f152,f74])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X0,X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | l1_orders_2(k3_waybel_2(X1,X2,X0))
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f102,f73])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))
      | v7_waybel_0(k3_waybel_2(X0,X1,X2))
      | ~ l1_orders_2(k3_waybel_2(X0,X1,X2))
      | ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f183,f99])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ v7_waybel_0(g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))
      | v7_waybel_0(k3_waybel_2(X0,X1,X2))
      | ~ l1_orders_2(k3_waybel_2(X0,X1,X2))
      | v2_struct_0(k3_waybel_2(X0,X1,X2))
      | ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f83,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(k3_waybel_2(X0,X1,X2)),u1_orders_2(k3_waybel_2(X0,X1,X2)))
      | ~ l1_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
      | k3_waybel_2(X0,X1,X2) != X3
      | ~ l1_waybel_0(X3,X0)
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_waybel_2(X0,X1,X2) = X3
                      | ( ! [X5] :
                            ( k11_lattice3(X0,X1,X5) != k1_funct_1(u1_waybel_0(X0,X3),sK6(X0,X1,X2,X3))
                            | k1_funct_1(u1_waybel_0(X0,X2),sK6(X0,X1,X2,X3)) != X5
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X3)) )
                      | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                    & ( ( ! [X6] :
                            ( ( k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,sK7(X0,X1,X2,X3,X6))
                              & k1_funct_1(u1_waybel_0(X0,X2),X6) = sK7(X0,X1,X2,X3,X6)
                              & m1_subset_1(sK7(X0,X1,X2,X3,X6),u1_struct_0(X0)) )
                            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                        & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                      | k3_waybel_2(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f61,f63,f62])).

fof(f62,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5)
              | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & m1_subset_1(X4,u1_struct_0(X3)) )
     => ( ! [X5] :
            ( k11_lattice3(X0,X1,X5) != k1_funct_1(u1_waybel_0(X0,X3),sK6(X0,X1,X2,X3))
            | k1_funct_1(u1_waybel_0(X0,X2),sK6(X0,X1,X2,X3)) != X5
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X6,X3,X2,X1,X0] :
      ( ? [X7] :
          ( k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,X7)
          & k1_funct_1(u1_waybel_0(X0,X2),X6) = X7
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,sK7(X0,X1,X2,X3,X6))
        & k1_funct_1(u1_waybel_0(X0,X2),X6) = sK7(X0,X1,X2,X3,X6)
        & m1_subset_1(sK7(X0,X1,X2,X3,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_waybel_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ! [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5)
                              | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5
                              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                          & m1_subset_1(X4,u1_struct_0(X3)) )
                      | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                    & ( ( ! [X6] :
                            ( ? [X7] :
                                ( k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,X7)
                                & k1_funct_1(u1_waybel_0(X0,X2),X6) = X7
                                & m1_subset_1(X7,u1_struct_0(X0)) )
                            | ~ m1_subset_1(X6,u1_struct_0(X3)) )
                        & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                      | k3_waybel_2(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_waybel_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ! [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5)
                              | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5
                              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                          & m1_subset_1(X4,u1_struct_0(X3)) )
                      | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                    & ( ( ! [X4] :
                            ( ? [X5] :
                                ( k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5)
                                & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5
                                & m1_subset_1(X5,u1_struct_0(X0)) )
                            | ~ m1_subset_1(X4,u1_struct_0(X3)) )
                        & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                      | k3_waybel_2(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k3_waybel_2(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ! [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5)
                              | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5
                              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                          & m1_subset_1(X4,u1_struct_0(X3)) )
                      | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                    & ( ( ! [X4] :
                            ( ? [X5] :
                                ( k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5)
                                & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5
                                & m1_subset_1(X5,u1_struct_0(X0)) )
                            | ~ m1_subset_1(X4,u1_struct_0(X3)) )
                        & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) )
                      | k3_waybel_2(X0,X1,X2) != X3 ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_waybel_2(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( ? [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5)
                              & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5
                              & m1_subset_1(X5,u1_struct_0(X0)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X3)) )
                      & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k3_waybel_2(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( ? [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5)
                              & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5
                              & m1_subset_1(X5,u1_struct_0(X0)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X3)) )
                      & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ l1_waybel_0(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k3_waybel_2(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X3))
                         => ? [X5] :
                              ( k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5)
                              & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5
                              & m1_subset_1(X5,u1_struct_0(X0)) ) )
                      & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_waybel_2)).

fof(f83,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
      | v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f120,plain,
    ( ~ v7_waybel_0(k3_waybel_2(sK0,sK1,sK2))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl8_3
  <=> v7_waybel_0(k3_waybel_2(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f412,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f411])).

fof(f411,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f410,f127])).

fof(f410,plain,
    ( ~ l1_orders_2(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f409,f69])).

fof(f69,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f409,plain,
    ( ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f408,f65])).

fof(f408,plain,
    ( v2_struct_0(sK0)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f407,f66])).

fof(f407,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f406,f67])).

fof(f406,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f405,f68])).

fof(f405,plain,
    ( v2_struct_0(sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f404,f71])).

fof(f404,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ v4_orders_2(sK2)
    | ~ l1_orders_2(sK2)
    | spl8_2 ),
    inference(resolution,[],[f292,f117])).

fof(f117,plain,
    ( ~ v4_orders_2(k3_waybel_2(sK0,sK1,sK2))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl8_2
  <=> v4_orders_2(k3_waybel_2(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f292,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_waybel_2(X0,X1,X2))
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X2)
      | ~ l1_orders_2(X2) ) ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_waybel_2(X0,X1,X2))
      | ~ l1_waybel_0(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X2)
      | ~ l1_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f198,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v4_orders_2(X0)
          | ~ v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) )
        & ( v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
          | ~ v4_orders_2(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_orders_2(X0)
      <=> v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l16_yellow_6)).

fof(f198,plain,(
    ! [X6,X8,X7] :
      ( ~ v4_orders_2(g1_orders_2(u1_struct_0(X8),u1_orders_2(X8)))
      | v4_orders_2(k3_waybel_2(X6,X7,X8))
      | ~ l1_waybel_0(X8,X6)
      | v2_struct_0(X8)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f197,f100])).

fof(f197,plain,(
    ! [X6,X8,X7] :
      ( ~ v4_orders_2(g1_orders_2(u1_struct_0(X8),u1_orders_2(X8)))
      | v4_orders_2(k3_waybel_2(X6,X7,X8))
      | ~ v6_waybel_0(k3_waybel_2(X6,X7,X8),X6)
      | ~ l1_waybel_0(X8,X6)
      | v2_struct_0(X8)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f196,f102])).

fof(f196,plain,(
    ! [X6,X8,X7] :
      ( ~ v4_orders_2(g1_orders_2(u1_struct_0(X8),u1_orders_2(X8)))
      | v4_orders_2(k3_waybel_2(X6,X7,X8))
      | ~ l1_waybel_0(k3_waybel_2(X6,X7,X8),X6)
      | ~ v6_waybel_0(k3_waybel_2(X6,X7,X8),X6)
      | ~ l1_waybel_0(X8,X6)
      | v2_struct_0(X8)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f195,f153])).

fof(f195,plain,(
    ! [X6,X8,X7] :
      ( ~ v4_orders_2(g1_orders_2(u1_struct_0(X8),u1_orders_2(X8)))
      | v4_orders_2(k3_waybel_2(X6,X7,X8))
      | ~ l1_orders_2(k3_waybel_2(X6,X7,X8))
      | ~ l1_waybel_0(k3_waybel_2(X6,X7,X8),X6)
      | ~ v6_waybel_0(k3_waybel_2(X6,X7,X8),X6)
      | ~ l1_waybel_0(X8,X6)
      | v2_struct_0(X8)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f185,f99])).

fof(f185,plain,(
    ! [X6,X8,X7] :
      ( ~ v4_orders_2(g1_orders_2(u1_struct_0(X8),u1_orders_2(X8)))
      | v4_orders_2(k3_waybel_2(X6,X7,X8))
      | ~ l1_orders_2(k3_waybel_2(X6,X7,X8))
      | v2_struct_0(k3_waybel_2(X6,X7,X8))
      | ~ l1_waybel_0(k3_waybel_2(X6,X7,X8),X6)
      | ~ v6_waybel_0(k3_waybel_2(X6,X7,X8),X6)
      | ~ l1_waybel_0(X8,X6)
      | v2_struct_0(X8)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | v2_struct_0(X6) ) ),
    inference(superposition,[],[f81,f111])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))
      | v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f124,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f72,f122,f119,f116,f113])).

fof(f72,plain,
    ( ~ l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0)
    | ~ v7_waybel_0(k3_waybel_2(sK0,sK1,sK2))
    | ~ v4_orders_2(k3_waybel_2(sK0,sK1,sK2))
    | v2_struct_0(k3_waybel_2(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:01:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (12806)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.42  % (12806)Refutation not found, incomplete strategy% (12806)------------------------------
% 0.21/0.42  % (12806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (12806)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (12806)Memory used [KB]: 10618
% 0.21/0.42  % (12806)Time elapsed: 0.004 s
% 0.21/0.42  % (12806)------------------------------
% 0.21/0.42  % (12806)------------------------------
% 0.21/0.45  % (12802)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (12790)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (12805)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.47  % (12788)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (12793)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (12786)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (12800)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (12791)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (12796)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (12792)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (12795)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (12799)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (12787)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (12801)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (12804)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (12798)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (12788)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  % (12787)Refutation not found, incomplete strategy% (12787)------------------------------
% 0.21/0.50  % (12787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12787)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12787)Memory used [KB]: 10618
% 0.21/0.50  % (12787)Time elapsed: 0.089 s
% 0.21/0.50  % (12787)------------------------------
% 0.21/0.50  % (12787)------------------------------
% 0.21/0.50  fof(f436,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f124,f412,f421,f428,f435])).
% 0.21/0.50  fof(f435,plain,(
% 0.21/0.50    ~spl8_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f434])).
% 0.21/0.50  fof(f434,plain,(
% 0.21/0.50    $false | ~spl8_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f433,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    (((~l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0) | ~v7_waybel_0(k3_waybel_2(sK0,sK1,sK2)) | ~v4_orders_2(k3_waybel_2(sK0,sK1,sK2)) | v2_struct_0(k3_waybel_2(sK0,sK1,sK2))) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f47,f46,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((~l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~v7_waybel_0(k3_waybel_2(X0,X1,X2)) | ~v4_orders_2(k3_waybel_2(X0,X1,X2)) | v2_struct_0(k3_waybel_2(X0,X1,X2))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~l1_waybel_0(k3_waybel_2(sK0,X1,X2),sK0) | ~v7_waybel_0(k3_waybel_2(sK0,X1,X2)) | ~v4_orders_2(k3_waybel_2(sK0,X1,X2)) | v2_struct_0(k3_waybel_2(sK0,X1,X2))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : ((~l1_waybel_0(k3_waybel_2(sK0,X1,X2),sK0) | ~v7_waybel_0(k3_waybel_2(sK0,X1,X2)) | ~v4_orders_2(k3_waybel_2(sK0,X1,X2)) | v2_struct_0(k3_waybel_2(sK0,X1,X2))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~l1_waybel_0(k3_waybel_2(sK0,sK1,X2),sK0) | ~v7_waybel_0(k3_waybel_2(sK0,sK1,X2)) | ~v4_orders_2(k3_waybel_2(sK0,sK1,X2)) | v2_struct_0(k3_waybel_2(sK0,sK1,X2))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ? [X2] : ((~l1_waybel_0(k3_waybel_2(sK0,sK1,X2),sK0) | ~v7_waybel_0(k3_waybel_2(sK0,sK1,X2)) | ~v4_orders_2(k3_waybel_2(sK0,sK1,X2)) | v2_struct_0(k3_waybel_2(sK0,sK1,X2))) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => ((~l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0) | ~v7_waybel_0(k3_waybel_2(sK0,sK1,sK2)) | ~v4_orders_2(k3_waybel_2(sK0,sK1,sK2)) | v2_struct_0(k3_waybel_2(sK0,sK1,sK2))) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((~l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~v7_waybel_0(k3_waybel_2(X0,X1,X2)) | ~v4_orders_2(k3_waybel_2(X0,X1,X2)) | v2_struct_0(k3_waybel_2(X0,X1,X2))) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((~l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~v7_waybel_0(k3_waybel_2(X0,X1,X2)) | ~v4_orders_2(k3_waybel_2(X0,X1,X2)) | v2_struct_0(k3_waybel_2(X0,X1,X2))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) & v7_waybel_0(k3_waybel_2(X0,X1,X2)) & v4_orders_2(k3_waybel_2(X0,X1,X2)) & ~v2_struct_0(k3_waybel_2(X0,X1,X2))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f15])).
% 0.21/0.50  fof(f15,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) & v7_waybel_0(k3_waybel_2(X0,X1,X2)) & v4_orders_2(k3_waybel_2(X0,X1,X2)) & ~v2_struct_0(k3_waybel_2(X0,X1,X2))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_9)).
% 0.21/0.50  fof(f433,plain,(
% 0.21/0.50    v2_struct_0(sK0) | ~spl8_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f432,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    l1_orders_2(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f432,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~spl8_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f431,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f431,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~spl8_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f430,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ~v2_struct_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f430,plain,(
% 0.21/0.50    v2_struct_0(sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~spl8_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f429,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    l1_waybel_0(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f429,plain,(
% 0.21/0.50    ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~spl8_1),
% 0.21/0.50    inference(resolution,[],[f114,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_struct_0(k3_waybel_2(X0,X1,X2)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) & ~v2_struct_0(k3_waybel_2(X0,X1,X2))) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) & ~v2_struct_0(k3_waybel_2(X0,X1,X2))) | (~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((l1_waybel_0(X2,X0) & ~v2_struct_0(X2) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) & ~v2_struct_0(k3_waybel_2(X0,X1,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_waybel_2)).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    v2_struct_0(k3_waybel_2(sK0,sK1,sK2)) | ~spl8_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f113])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl8_1 <=> v2_struct_0(k3_waybel_2(sK0,sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.50  fof(f428,plain,(
% 0.21/0.50    spl8_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f427])).
% 0.21/0.50  fof(f427,plain,(
% 0.21/0.50    $false | spl8_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f426,f65])).
% 0.21/0.50  fof(f426,plain,(
% 0.21/0.50    v2_struct_0(sK0) | spl8_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f425,f66])).
% 0.21/0.50  fof(f425,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | v2_struct_0(sK0) | spl8_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f424,f67])).
% 0.21/0.50  fof(f424,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | spl8_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f423,f68])).
% 0.21/0.50  fof(f423,plain,(
% 0.21/0.50    v2_struct_0(sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | spl8_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f422,f71])).
% 0.21/0.50  fof(f422,plain,(
% 0.21/0.50    ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | spl8_4),
% 0.21/0.50    inference(resolution,[],[f123,f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)) | (~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((l1_waybel_0(X2,X0) & ~v2_struct_0(X2) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) & v6_waybel_0(k3_waybel_2(X0,X1,X2),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_waybel_2)).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ~l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0) | spl8_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f122])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl8_4 <=> l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.50  fof(f421,plain,(
% 0.21/0.50    spl8_3),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f420])).
% 0.21/0.50  fof(f420,plain,(
% 0.21/0.50    $false | spl8_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f419,f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    l1_orders_2(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f126,f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    l1_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f74,f66])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    l1_orders_2(sK2) | ~l1_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f73,f71])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | l1_orders_2(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.21/0.50  fof(f419,plain,(
% 0.21/0.50    ~l1_orders_2(sK2) | spl8_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f418,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    v7_waybel_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f418,plain,(
% 0.21/0.50    ~v7_waybel_0(sK2) | ~l1_orders_2(sK2) | spl8_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f417,f65])).
% 0.21/0.50  fof(f417,plain,(
% 0.21/0.50    v2_struct_0(sK0) | ~v7_waybel_0(sK2) | ~l1_orders_2(sK2) | spl8_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f416,f66])).
% 0.21/0.50  fof(f416,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v7_waybel_0(sK2) | ~l1_orders_2(sK2) | spl8_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f415,f67])).
% 0.21/0.50  fof(f415,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v7_waybel_0(sK2) | ~l1_orders_2(sK2) | spl8_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f414,f68])).
% 0.21/0.50  fof(f414,plain,(
% 0.21/0.50    v2_struct_0(sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v7_waybel_0(sK2) | ~l1_orders_2(sK2) | spl8_3),
% 0.21/0.50    inference(subsumption_resolution,[],[f413,f71])).
% 0.21/0.50  fof(f413,plain,(
% 0.21/0.50    ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v7_waybel_0(sK2) | ~l1_orders_2(sK2) | spl8_3),
% 0.21/0.50    inference(resolution,[],[f120,f270])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v7_waybel_0(k3_waybel_2(X0,X1,X2)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~v7_waybel_0(X2) | ~l1_orders_2(X2)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f266])).
% 0.21/0.50  fof(f266,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v7_waybel_0(k3_waybel_2(X0,X1,X2)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~v7_waybel_0(X2) | ~l1_orders_2(X2) | v2_struct_0(X2)) )),
% 0.21/0.50    inference(resolution,[],[f190,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X0] : (v7_waybel_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) | ~v7_waybel_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ! [X0] : (((v7_waybel_0(X0) | ~v7_waybel_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) & (v7_waybel_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) | ~v7_waybel_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : ((v7_waybel_0(X0) <=> v7_waybel_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : ((v7_waybel_0(X0) <=> v7_waybel_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(X0) <=> v7_waybel_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l15_yellow_6)).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v7_waybel_0(g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) | v7_waybel_0(k3_waybel_2(X0,X1,X2)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f189,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v7_waybel_0(g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) | v7_waybel_0(k3_waybel_2(X0,X1,X2)) | ~v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f188,f102])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v7_waybel_0(g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) | v7_waybel_0(k3_waybel_2(X0,X1,X2)) | ~l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f187,f153])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (l1_orders_2(k3_waybel_2(X1,X2,X0)) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | v2_struct_0(X1) | ~l1_waybel_0(X0,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f152,f74])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_waybel_0(X0,X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | v2_struct_0(X1) | l1_orders_2(k3_waybel_2(X1,X2,X0)) | ~l1_struct_0(X1)) )),
% 0.21/0.50    inference(resolution,[],[f102,f73])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v7_waybel_0(g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) | v7_waybel_0(k3_waybel_2(X0,X1,X2)) | ~l1_orders_2(k3_waybel_2(X0,X1,X2)) | ~l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f183,f99])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v7_waybel_0(g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) | v7_waybel_0(k3_waybel_2(X0,X1,X2)) | ~l1_orders_2(k3_waybel_2(X0,X1,X2)) | v2_struct_0(k3_waybel_2(X0,X1,X2)) | ~l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(superposition,[],[f83,f111])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) = g1_orders_2(u1_struct_0(k3_waybel_2(X0,X1,X2)),u1_orders_2(k3_waybel_2(X0,X1,X2))) | ~l1_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~v6_waybel_0(k3_waybel_2(X0,X1,X2),X0) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) | k3_waybel_2(X0,X1,X2) != X3 | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k3_waybel_2(X0,X1,X2) = X3 | (! [X5] : (k11_lattice3(X0,X1,X5) != k1_funct_1(u1_waybel_0(X0,X3),sK6(X0,X1,X2,X3)) | k1_funct_1(u1_waybel_0(X0,X2),sK6(X0,X1,X2,X3)) != X5 | ~m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X3))) | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) & ((! [X6] : ((k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,sK7(X0,X1,X2,X3,X6)) & k1_funct_1(u1_waybel_0(X0,X2),X6) = sK7(X0,X1,X2,X3,X6) & m1_subset_1(sK7(X0,X1,X2,X3,X6),u1_struct_0(X0))) | ~m1_subset_1(X6,u1_struct_0(X3))) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) | k3_waybel_2(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f61,f63,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ! [X3,X2,X1,X0] : (? [X4] : (! [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5) | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5 | ~m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X3))) => (! [X5] : (k11_lattice3(X0,X1,X5) != k1_funct_1(u1_waybel_0(X0,X3),sK6(X0,X1,X2,X3)) | k1_funct_1(u1_waybel_0(X0,X2),sK6(X0,X1,X2,X3)) != X5 | ~m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X3))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ! [X6,X3,X2,X1,X0] : (? [X7] : (k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,X7) & k1_funct_1(u1_waybel_0(X0,X2),X6) = X7 & m1_subset_1(X7,u1_struct_0(X0))) => (k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,sK7(X0,X1,X2,X3,X6)) & k1_funct_1(u1_waybel_0(X0,X2),X6) = sK7(X0,X1,X2,X3,X6) & m1_subset_1(sK7(X0,X1,X2,X3,X6),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k3_waybel_2(X0,X1,X2) = X3 | ? [X4] : (! [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5) | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5 | ~m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X3))) | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) & ((! [X6] : (? [X7] : (k1_funct_1(u1_waybel_0(X0,X3),X6) = k11_lattice3(X0,X1,X7) & k1_funct_1(u1_waybel_0(X0,X2),X6) = X7 & m1_subset_1(X7,u1_struct_0(X0))) | ~m1_subset_1(X6,u1_struct_0(X3))) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) | k3_waybel_2(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k3_waybel_2(X0,X1,X2) = X3 | ? [X4] : (! [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5) | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5 | ~m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X3))) | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) & ((! [X4] : (? [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5) & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X3))) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) | k3_waybel_2(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k3_waybel_2(X0,X1,X2) = X3 | (? [X4] : (! [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) != k11_lattice3(X0,X1,X5) | k1_funct_1(u1_waybel_0(X0,X2),X4) != X5 | ~m1_subset_1(X5,u1_struct_0(X0))) & m1_subset_1(X4,u1_struct_0(X3))) | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))) & ((! [X4] : (? [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5) & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X3))) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))) | k3_waybel_2(X0,X1,X2) != X3)) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k3_waybel_2(X0,X1,X2) = X3 <=> (! [X4] : (? [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5) & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X3))) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k3_waybel_2(X0,X1,X2) = X3 <=> (! [X4] : (? [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5) & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X3))) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)))) | (~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0))) | (~l1_waybel_0(X2,X0) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((l1_waybel_0(X3,X0) & v6_waybel_0(X3,X0)) => (k3_waybel_2(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X3)) => ? [X5] : (k1_funct_1(u1_waybel_0(X0,X3),X4) = k11_lattice3(X0,X1,X5) & k1_funct_1(u1_waybel_0(X0,X2),X4) = X5 & m1_subset_1(X5,u1_struct_0(X0)))) & g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) = g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_waybel_2)).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0] : (~v7_waybel_0(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) | v7_waybel_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    ~v7_waybel_0(k3_waybel_2(sK0,sK1,sK2)) | spl8_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f119])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl8_3 <=> v7_waybel_0(k3_waybel_2(sK0,sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.50  fof(f412,plain,(
% 0.21/0.50    spl8_2),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f411])).
% 0.21/0.50  fof(f411,plain,(
% 0.21/0.50    $false | spl8_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f410,f127])).
% 0.21/0.50  fof(f410,plain,(
% 0.21/0.50    ~l1_orders_2(sK2) | spl8_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f409,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    v4_orders_2(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  fof(f409,plain,(
% 0.21/0.50    ~v4_orders_2(sK2) | ~l1_orders_2(sK2) | spl8_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f408,f65])).
% 0.21/0.50  fof(f408,plain,(
% 0.21/0.50    v2_struct_0(sK0) | ~v4_orders_2(sK2) | ~l1_orders_2(sK2) | spl8_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f407,f66])).
% 0.21/0.50  fof(f407,plain,(
% 0.21/0.50    ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v4_orders_2(sK2) | ~l1_orders_2(sK2) | spl8_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f406,f67])).
% 0.21/0.50  fof(f406,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v4_orders_2(sK2) | ~l1_orders_2(sK2) | spl8_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f405,f68])).
% 0.21/0.50  fof(f405,plain,(
% 0.21/0.50    v2_struct_0(sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v4_orders_2(sK2) | ~l1_orders_2(sK2) | spl8_2),
% 0.21/0.50    inference(subsumption_resolution,[],[f404,f71])).
% 0.21/0.50  fof(f404,plain,(
% 0.21/0.50    ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~v4_orders_2(sK2) | ~l1_orders_2(sK2) | spl8_2),
% 0.21/0.50    inference(resolution,[],[f292,f117])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ~v4_orders_2(k3_waybel_2(sK0,sK1,sK2)) | spl8_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f116])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    spl8_2 <=> v4_orders_2(k3_waybel_2(sK0,sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v4_orders_2(k3_waybel_2(X0,X1,X2)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~v4_orders_2(X2) | ~l1_orders_2(X2)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f288])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v4_orders_2(k3_waybel_2(X0,X1,X2)) | ~l1_waybel_0(X2,X0) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~v4_orders_2(X2) | ~l1_orders_2(X2) | v2_struct_0(X2)) )),
% 0.21/0.50    inference(resolution,[],[f198,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X0] : (v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) | ~v4_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ! [X0] : (((v4_orders_2(X0) | ~v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) & (v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) | ~v4_orders_2(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : ((v4_orders_2(X0) <=> v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : ((v4_orders_2(X0) <=> v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => (v4_orders_2(X0) <=> v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l16_yellow_6)).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    ( ! [X6,X8,X7] : (~v4_orders_2(g1_orders_2(u1_struct_0(X8),u1_orders_2(X8))) | v4_orders_2(k3_waybel_2(X6,X7,X8)) | ~l1_waybel_0(X8,X6) | v2_struct_0(X8) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_orders_2(X6) | v2_struct_0(X6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f197,f100])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    ( ! [X6,X8,X7] : (~v4_orders_2(g1_orders_2(u1_struct_0(X8),u1_orders_2(X8))) | v4_orders_2(k3_waybel_2(X6,X7,X8)) | ~v6_waybel_0(k3_waybel_2(X6,X7,X8),X6) | ~l1_waybel_0(X8,X6) | v2_struct_0(X8) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_orders_2(X6) | v2_struct_0(X6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f196,f102])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    ( ! [X6,X8,X7] : (~v4_orders_2(g1_orders_2(u1_struct_0(X8),u1_orders_2(X8))) | v4_orders_2(k3_waybel_2(X6,X7,X8)) | ~l1_waybel_0(k3_waybel_2(X6,X7,X8),X6) | ~v6_waybel_0(k3_waybel_2(X6,X7,X8),X6) | ~l1_waybel_0(X8,X6) | v2_struct_0(X8) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_orders_2(X6) | v2_struct_0(X6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f195,f153])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    ( ! [X6,X8,X7] : (~v4_orders_2(g1_orders_2(u1_struct_0(X8),u1_orders_2(X8))) | v4_orders_2(k3_waybel_2(X6,X7,X8)) | ~l1_orders_2(k3_waybel_2(X6,X7,X8)) | ~l1_waybel_0(k3_waybel_2(X6,X7,X8),X6) | ~v6_waybel_0(k3_waybel_2(X6,X7,X8),X6) | ~l1_waybel_0(X8,X6) | v2_struct_0(X8) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_orders_2(X6) | v2_struct_0(X6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f185,f99])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ( ! [X6,X8,X7] : (~v4_orders_2(g1_orders_2(u1_struct_0(X8),u1_orders_2(X8))) | v4_orders_2(k3_waybel_2(X6,X7,X8)) | ~l1_orders_2(k3_waybel_2(X6,X7,X8)) | v2_struct_0(k3_waybel_2(X6,X7,X8)) | ~l1_waybel_0(k3_waybel_2(X6,X7,X8),X6) | ~v6_waybel_0(k3_waybel_2(X6,X7,X8),X6) | ~l1_waybel_0(X8,X6) | v2_struct_0(X8) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l1_orders_2(X6) | v2_struct_0(X6)) )),
% 0.21/0.50    inference(superposition,[],[f81,f111])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_orders_2(g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))) | v4_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl8_1 | ~spl8_2 | ~spl8_3 | ~spl8_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f72,f122,f119,f116,f113])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ~l1_waybel_0(k3_waybel_2(sK0,sK1,sK2),sK0) | ~v7_waybel_0(k3_waybel_2(sK0,sK1,sK2)) | ~v4_orders_2(k3_waybel_2(sK0,sK1,sK2)) | v2_struct_0(k3_waybel_2(sK0,sK1,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f48])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (12788)------------------------------
% 0.21/0.50  % (12788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12788)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (12788)Memory used [KB]: 11001
% 0.21/0.50  % (12788)Time elapsed: 0.086 s
% 0.21/0.50  % (12788)------------------------------
% 0.21/0.50  % (12788)------------------------------
% 0.21/0.50  % (12803)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (12785)Success in time 0.148 s
%------------------------------------------------------------------------------
