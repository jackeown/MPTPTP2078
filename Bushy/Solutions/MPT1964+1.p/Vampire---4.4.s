%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t13_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:03 EDT 2019

% Result     : Theorem 2.71s
% Output     : Refutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 446 expanded)
%              Number of leaves         :   24 ( 138 expanded)
%              Depth                    :   25
%              Number of atoms          :  712 (3015 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26844,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f192,f199,f206,f210,f26554,f26583,f26594,f26605,f26616,f26627,f26632,f26843])).

fof(f26843,plain,
    ( ~ spl9_8
    | spl9_2241
    | ~ spl9_2242
    | ~ spl9_2244
    | ~ spl9_2246
    | ~ spl9_2248 ),
    inference(avatar_contradiction_clause,[],[f26842])).

fof(f26842,plain,
    ( $false
    | ~ spl9_8
    | ~ spl9_2241
    | ~ spl9_2242
    | ~ spl9_2244
    | ~ spl9_2246
    | ~ spl9_2248 ),
    inference(subsumption_resolution,[],[f26841,f26615])).

fof(f26615,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ spl9_2246 ),
    inference(avatar_component_clause,[],[f26614])).

fof(f26614,plain,
    ( spl9_2246
  <=> r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2246])])).

fof(f26841,plain,
    ( ~ r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ spl9_8
    | ~ spl9_2241
    | ~ spl9_2242
    | ~ spl9_2244
    | ~ spl9_2248 ),
    inference(subsumption_resolution,[],[f26840,f26626])).

fof(f26626,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ spl9_2248 ),
    inference(avatar_component_clause,[],[f26625])).

fof(f26625,plain,
    ( spl9_2248
  <=> r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2248])])).

fof(f26840,plain,
    ( ~ r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ spl9_8
    | ~ spl9_2241
    | ~ spl9_2242
    | ~ spl9_2244 ),
    inference(resolution,[],[f26817,f209])).

fof(f209,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k3_xboole_0(X4,X5),sK1)
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl9_8
  <=> ! [X5,X4] :
        ( r2_hidden(k3_xboole_0(X4,X5),sK1)
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f26817,plain,
    ( ~ r2_hidden(k3_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ spl9_2241
    | ~ spl9_2242
    | ~ spl9_2244 ),
    inference(subsumption_resolution,[],[f26816,f26604])).

fof(f26604,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_2244 ),
    inference(avatar_component_clause,[],[f26603])).

fof(f26603,plain,
    ( spl9_2244
  <=> m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2244])])).

fof(f26816,plain,
    ( ~ r2_hidden(k3_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_2241
    | ~ spl9_2242 ),
    inference(subsumption_resolution,[],[f26812,f26593])).

fof(f26593,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_2242 ),
    inference(avatar_component_clause,[],[f26592])).

fof(f26592,plain,
    ( spl9_2242
  <=> m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2242])])).

fof(f26812,plain,
    ( ~ r2_hidden(k3_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_2241 ),
    inference(superposition,[],[f26582,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k3_xboole_0(X1,X2) = k12_lattice3(k3_yellow_1(X0),X1,X2)
            & k13_lattice3(k3_yellow_1(X0),X1,X2) = k2_xboole_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t13_waybel_7.p',t17_yellow_1)).

fof(f26582,plain,
    ( ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ spl9_2241 ),
    inference(avatar_component_clause,[],[f26581])).

fof(f26581,plain,
    ( spl9_2241
  <=> ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2241])])).

fof(f26632,plain,(
    spl9_2239 ),
    inference(avatar_contradiction_clause,[],[f26631])).

fof(f26631,plain,
    ( $false
    | ~ spl9_2239 ),
    inference(subsumption_resolution,[],[f26630,f127])).

fof(f127,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t13_waybel_7.p',dt_k3_yellow_1)).

fof(f26630,plain,
    ( ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ spl9_2239 ),
    inference(subsumption_resolution,[],[f26629,f119])).

fof(f119,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t13_waybel_7.p',fc7_yellow_1)).

fof(f26629,plain,
    ( v2_struct_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ spl9_2239 ),
    inference(subsumption_resolution,[],[f26628,f125])).

fof(f125,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0] :
      ( v11_waybel_1(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t13_waybel_7.p',fc1_waybel_7)).

fof(f26628,plain,
    ( ~ v11_waybel_1(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ spl9_2239 ),
    inference(resolution,[],[f26576,f137])).

fof(f137,plain,(
    ! [X0] :
      ( v2_lattice3(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v10_waybel_1(X0)
        & v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( v10_waybel_1(X0)
        & v2_waybel_1(X0)
        & v3_yellow_0(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v11_waybel_1(X0)
          & ~ v2_struct_0(X0) )
       => ( v10_waybel_1(X0)
          & v2_waybel_1(X0)
          & v3_yellow_0(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t13_waybel_7.p',cc8_waybel_1)).

fof(f26576,plain,
    ( ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ spl9_2239 ),
    inference(avatar_component_clause,[],[f26575])).

fof(f26575,plain,
    ( spl9_2239
  <=> ~ v2_lattice3(k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2239])])).

fof(f26627,plain,
    ( ~ spl9_2239
    | spl9_2248
    | spl9_1 ),
    inference(avatar_split_clause,[],[f26620,f184,f26625,f26575])).

fof(f184,plain,
    ( spl9_1
  <=> ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f26620,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26619,f123])).

fof(f123,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f26619,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26618,f127])).

fof(f26618,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26617,f109])).

fof(f109,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,
    ( ( ( ~ r2_hidden(k3_xboole_0(sK2,sK3),sK1)
        & r2_hidden(sK3,sK1)
        & r2_hidden(sK2,sK1) )
      | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) )
    & ( ! [X4,X5] :
          ( r2_hidden(k3_xboole_0(X4,X5),sK1)
          | ~ r2_hidden(X5,sK1)
          | ~ r2_hidden(X4,sK1) )
      | v2_waybel_0(sK1,k3_yellow_1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    & v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f93,f95,f94])).

fof(f94,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( ~ r2_hidden(k3_xboole_0(X2,X3),X1)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1) )
          | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
        & ( ! [X4,X5] :
              ( r2_hidden(k3_xboole_0(X4,X5),X1)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          | v2_waybel_0(X1,k3_yellow_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0)) )
   => ( ( ? [X3,X2] :
            ( ~ r2_hidden(k3_xboole_0(X2,X3),sK1)
            & r2_hidden(X3,sK1)
            & r2_hidden(X2,sK1) )
        | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) )
      & ( ! [X5,X4] :
            ( r2_hidden(k3_xboole_0(X4,X5),sK1)
            | ~ r2_hidden(X5,sK1)
            | ~ r2_hidden(X4,sK1) )
        | v2_waybel_0(sK1,k3_yellow_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
      & v13_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ! [X1] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k3_xboole_0(X2,X3),X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k3_xboole_0(sK2,sK3),X1)
        & r2_hidden(sK3,X1)
        & r2_hidden(sK2,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f93,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( ~ r2_hidden(k3_xboole_0(X2,X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X4,X5] :
            ( r2_hidden(k3_xboole_0(X4,X5),X1)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | v2_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(rectify,[],[f92])).

fof(f92,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( ~ r2_hidden(k3_xboole_0(X2,X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X2,X3] :
            ( r2_hidden(k3_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) )
        | v2_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(flattening,[],[f91])).

fof(f91,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( ~ r2_hidden(k3_xboole_0(X2,X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | ~ v2_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X2,X3] :
            ( r2_hidden(k3_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) )
        | v2_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2,X3] :
            ( r2_hidden(k3_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ? [X0,X1] :
      ( ( v2_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2,X3] :
            ( r2_hidden(k3_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0)) )
       => ( v2_waybel_0(X1,k3_yellow_1(X0))
        <=> ! [X2,X3] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => r2_hidden(k3_xboole_0(X2,X3),X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v13_waybel_0(X1,k3_yellow_1(X0)) )
     => ( v2_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X2,X1) )
           => r2_hidden(k3_xboole_0(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t13_waybel_7.p',t13_waybel_7)).

fof(f26617,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26566,f110])).

fof(f110,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f96])).

fof(f26566,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(resolution,[],[f185,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ( ~ r2_hidden(k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
                & r2_hidden(sK5(X0,X1),X1)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f98,f100,f99])).

fof(f99,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(k12_lattice3(X0,sK4(X0,X1),X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k12_lattice3(X0,X2,sK5(X0,X1)),X1)
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      | ~ r2_hidden(X3,X1)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0) )
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t13_waybel_7.p',t41_waybel_0)).

fof(f185,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f184])).

fof(f26616,plain,
    ( ~ spl9_2239
    | spl9_2246
    | spl9_1 ),
    inference(avatar_split_clause,[],[f26609,f184,f26614,f26575])).

fof(f26609,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26608,f123])).

fof(f26608,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26607,f127])).

fof(f26607,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26606,f109])).

fof(f26606,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26565,f110])).

fof(f26565,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(resolution,[],[f185,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | r2_hidden(sK5(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f26605,plain,
    ( ~ spl9_2239
    | spl9_2244
    | spl9_1 ),
    inference(avatar_split_clause,[],[f26598,f184,f26603,f26575])).

fof(f26598,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26597,f123])).

fof(f26597,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26596,f127])).

fof(f26596,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26595,f109])).

fof(f26595,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26564,f110])).

fof(f26564,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(resolution,[],[f185,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f26594,plain,
    ( ~ spl9_2239
    | spl9_2242
    | spl9_1 ),
    inference(avatar_split_clause,[],[f26587,f184,f26592,f26575])).

fof(f26587,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26586,f123])).

fof(f26586,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26585,f127])).

fof(f26585,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26584,f109])).

fof(f26584,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26563,f110])).

fof(f26563,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(resolution,[],[f185,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f26583,plain,
    ( ~ spl9_2239
    | ~ spl9_2241
    | spl9_1 ),
    inference(avatar_split_clause,[],[f26570,f184,f26581,f26575])).

fof(f26570,plain,
    ( ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26569,f123])).

fof(f26569,plain,
    ( ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26568,f127])).

fof(f26568,plain,
    ( ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26567,f109])).

fof(f26567,plain,
    ( ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f26562,f110])).

fof(f26562,plain,
    ( ~ r2_hidden(k12_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v2_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(resolution,[],[f185,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(X1,X0)
      | ~ r2_hidden(k12_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f26554,plain,
    ( ~ spl9_0
    | spl9_3
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f26553])).

fof(f26553,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f26552,f1422])).

fof(f1422,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_6 ),
    inference(resolution,[],[f1119,f110])).

fof(f1119,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | m1_subset_1(sK2,X0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f205,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t13_waybel_7.p',t4_subset)).

fof(f205,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl9_6
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f26552,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_0
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f26551,f1400])).

fof(f1400,plain,
    ( m1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_4 ),
    inference(resolution,[],[f1115,f110])).

fof(f1115,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | m1_subset_1(sK3,X0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f198,f173])).

fof(f198,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl9_4
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f26551,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_0
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f26550,f198])).

fof(f26550,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_0
    | ~ spl9_3
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f26539,f205])).

fof(f26539,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK3,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_0
    | ~ spl9_3 ),
    inference(resolution,[],[f12174,f191])).

fof(f191,plain,
    ( ~ r2_hidden(k3_xboole_0(sK2,sK3),sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl9_3
  <=> ~ r2_hidden(k3_xboole_0(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f12174,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k3_xboole_0(X4,X5),sK1)
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,u1_struct_0(k3_yellow_1(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(sK0))) )
    | ~ spl9_0 ),
    inference(superposition,[],[f11390,f156])).

fof(f11390,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k12_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl9_0 ),
    inference(subsumption_resolution,[],[f11389,f110])).

fof(f11389,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(k12_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl9_0 ),
    inference(subsumption_resolution,[],[f11388,f182])).

fof(f182,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl9_0
  <=> v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f11388,plain,(
    ! [X0,X1] :
      ( ~ v2_waybel_0(sK1,k3_yellow_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(k12_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f7683,f109])).

fof(f7683,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v13_waybel_0(X1,k3_yellow_1(X2))
      | ~ v2_waybel_0(X1,k3_yellow_1(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(k12_lattice3(k3_yellow_1(X2),X0,X3),X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(subsumption_resolution,[],[f7682,f119])).

fof(f7682,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X2))
      | r2_hidden(k12_lattice3(k3_yellow_1(X2),X0,X3),X1)
      | ~ r2_hidden(X3,X1)
      | v2_struct_0(k3_yellow_1(X2)) ) ),
    inference(subsumption_resolution,[],[f7681,f127])).

fof(f7681,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v2_waybel_0(X1,k3_yellow_1(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))
      | ~ v13_waybel_0(X1,k3_yellow_1(X2))
      | ~ l1_orders_2(k3_yellow_1(X2))
      | r2_hidden(k12_lattice3(k3_yellow_1(X2),X0,X3),X1)
      | ~ r2_hidden(X3,X1)
      | v2_struct_0(k3_yellow_1(X2)) ) ),
    inference(resolution,[],[f5458,f125])).

fof(f5458,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v11_waybel_1(X3)
      | ~ r2_hidden(X2,X1)
      | ~ v2_waybel_0(X1,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v13_waybel_0(X1,X3)
      | ~ l1_orders_2(X3)
      | r2_hidden(k12_lattice3(X3,X2,X0),X1)
      | ~ r2_hidden(X0,X1)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f5457,f135])).

fof(f135,plain,(
    ! [X0] :
      ( v5_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f5457,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ v2_waybel_0(X1,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v13_waybel_0(X1,X3)
      | ~ l1_orders_2(X3)
      | r2_hidden(k12_lattice3(X3,X2,X0),X1)
      | ~ v5_orders_2(X3)
      | ~ v11_waybel_1(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f5456])).

fof(f5456,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ v2_waybel_0(X1,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v13_waybel_0(X1,X3)
      | ~ l1_orders_2(X3)
      | r2_hidden(k12_lattice3(X3,X2,X0),X1)
      | ~ v5_orders_2(X3)
      | ~ v11_waybel_1(X3)
      | v2_struct_0(X3)
      | ~ l1_orders_2(X3) ) ),
    inference(resolution,[],[f5057,f137])).

fof(f5057,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v2_lattice3(X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f5056,f173])).

fof(f5056,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f141,f173])).

fof(f141,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k12_lattice3(X0,X4,X5),X1)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f210,plain,
    ( spl9_0
    | spl9_8 ),
    inference(avatar_split_clause,[],[f111,f208,f181])).

fof(f111,plain,(
    ! [X4,X5] :
      ( r2_hidden(k3_xboole_0(X4,X5),sK1)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X4,sK1)
      | v2_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f206,plain,
    ( ~ spl9_1
    | spl9_6 ),
    inference(avatar_split_clause,[],[f112,f204,f184])).

fof(f112,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

fof(f199,plain,
    ( ~ spl9_1
    | spl9_4 ),
    inference(avatar_split_clause,[],[f113,f197,f184])).

fof(f113,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

fof(f192,plain,
    ( ~ spl9_1
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f114,f190,f184])).

fof(f114,plain,
    ( ~ r2_hidden(k3_xboole_0(sK2,sK3),sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f96])).
%------------------------------------------------------------------------------
