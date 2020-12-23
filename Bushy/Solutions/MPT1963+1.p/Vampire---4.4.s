%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t12_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:03 EDT 2019

% Result     : Theorem 2.70s
% Output     : Refutation 2.70s
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
fof(f27673,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f192,f199,f206,f210,f27237,f27266,f27277,f27288,f27299,f27310,f27315,f27672])).

fof(f27672,plain,
    ( ~ spl9_8
    | spl9_1993
    | ~ spl9_1994
    | ~ spl9_1996
    | ~ spl9_1998
    | ~ spl9_2000 ),
    inference(avatar_contradiction_clause,[],[f27671])).

fof(f27671,plain,
    ( $false
    | ~ spl9_8
    | ~ spl9_1993
    | ~ spl9_1994
    | ~ spl9_1996
    | ~ spl9_1998
    | ~ spl9_2000 ),
    inference(subsumption_resolution,[],[f27670,f27298])).

fof(f27298,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ spl9_1998 ),
    inference(avatar_component_clause,[],[f27297])).

fof(f27297,plain,
    ( spl9_1998
  <=> r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1998])])).

fof(f27670,plain,
    ( ~ r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ spl9_8
    | ~ spl9_1993
    | ~ spl9_1994
    | ~ spl9_1996
    | ~ spl9_2000 ),
    inference(subsumption_resolution,[],[f27669,f27309])).

fof(f27309,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ spl9_2000 ),
    inference(avatar_component_clause,[],[f27308])).

fof(f27308,plain,
    ( spl9_2000
  <=> r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2000])])).

fof(f27669,plain,
    ( ~ r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ spl9_8
    | ~ spl9_1993
    | ~ spl9_1994
    | ~ spl9_1996 ),
    inference(resolution,[],[f27555,f209])).

fof(f209,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k2_xboole_0(X4,X5),sK1)
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1) )
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl9_8
  <=> ! [X5,X4] :
        ( r2_hidden(k2_xboole_0(X4,X5),sK1)
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f27555,plain,
    ( ~ r2_hidden(k2_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ spl9_1993
    | ~ spl9_1994
    | ~ spl9_1996 ),
    inference(subsumption_resolution,[],[f27554,f27287])).

fof(f27287,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_1996 ),
    inference(avatar_component_clause,[],[f27286])).

fof(f27286,plain,
    ( spl9_1996
  <=> m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1996])])).

fof(f27554,plain,
    ( ~ r2_hidden(k2_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_1993
    | ~ spl9_1994 ),
    inference(subsumption_resolution,[],[f27550,f27276])).

fof(f27276,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_1994 ),
    inference(avatar_component_clause,[],[f27275])).

fof(f27275,plain,
    ( spl9_1994
  <=> m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1994])])).

fof(f27550,plain,
    ( ~ r2_hidden(k2_xboole_0(sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_1993 ),
    inference(superposition,[],[f27265,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2) )
          | ~ m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k3_yellow_1(X0)))
         => ( k12_lattice3(k3_yellow_1(X0),X1,X2) = k3_xboole_0(X1,X2)
            & k2_xboole_0(X1,X2) = k13_lattice3(k3_yellow_1(X0),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t12_waybel_7.p',t17_yellow_1)).

fof(f27265,plain,
    ( ~ r2_hidden(k13_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ spl9_1993 ),
    inference(avatar_component_clause,[],[f27264])).

fof(f27264,plain,
    ( spl9_1993
  <=> ~ r2_hidden(k13_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1993])])).

fof(f27315,plain,(
    spl9_1991 ),
    inference(avatar_contradiction_clause,[],[f27314])).

fof(f27314,plain,
    ( $false
    | ~ spl9_1991 ),
    inference(subsumption_resolution,[],[f27313,f127])).

fof(f127,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t12_waybel_7.p',dt_k3_yellow_1)).

fof(f27313,plain,
    ( ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1991 ),
    inference(subsumption_resolution,[],[f27312,f119])).

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
    file('/export/starexec/sandbox/benchmark/waybel_7__t12_waybel_7.p',fc7_yellow_1)).

fof(f27312,plain,
    ( v2_struct_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1991 ),
    inference(subsumption_resolution,[],[f27311,f125])).

fof(f125,plain,(
    ! [X0] : v11_waybel_1(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0] :
      ( v11_waybel_1(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t12_waybel_7.p',fc1_waybel_7)).

fof(f27311,plain,
    ( ~ v11_waybel_1(k3_yellow_1(sK0))
    | v2_struct_0(k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1991 ),
    inference(resolution,[],[f27259,f136])).

fof(f136,plain,(
    ! [X0] :
      ( v1_lattice3(X0)
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
    file('/export/starexec/sandbox/benchmark/waybel_7__t12_waybel_7.p',cc8_waybel_1)).

fof(f27259,plain,
    ( ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ spl9_1991 ),
    inference(avatar_component_clause,[],[f27258])).

fof(f27258,plain,
    ( spl9_1991
  <=> ~ v1_lattice3(k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1991])])).

fof(f27310,plain,
    ( ~ spl9_1991
    | spl9_2000
    | spl9_1 ),
    inference(avatar_split_clause,[],[f27303,f184,f27308,f27258])).

fof(f184,plain,
    ( spl9_1
  <=> ~ v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f27303,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27302,f123])).

fof(f123,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f27302,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27301,f127])).

fof(f27301,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27300,f109])).

fof(f109,plain,(
    v12_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,
    ( ( ( ~ r2_hidden(k2_xboole_0(sK2,sK3),sK1)
        & r2_hidden(sK3,sK1)
        & r2_hidden(sK2,sK1) )
      | ~ v1_waybel_0(sK1,k3_yellow_1(sK0)) )
    & ( ! [X4,X5] :
          ( r2_hidden(k2_xboole_0(X4,X5),sK1)
          | ~ r2_hidden(X5,sK1)
          | ~ r2_hidden(X4,sK1) )
      | v1_waybel_0(sK1,k3_yellow_1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    & v12_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f93,f95,f94])).

fof(f94,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( ~ r2_hidden(k2_xboole_0(X2,X3),X1)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1) )
          | ~ v1_waybel_0(X1,k3_yellow_1(X0)) )
        & ( ! [X4,X5] :
              ( r2_hidden(k2_xboole_0(X4,X5),X1)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          | v1_waybel_0(X1,k3_yellow_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v12_waybel_0(X1,k3_yellow_1(X0)) )
   => ( ( ? [X3,X2] :
            ( ~ r2_hidden(k2_xboole_0(X2,X3),sK1)
            & r2_hidden(X3,sK1)
            & r2_hidden(X2,sK1) )
        | ~ v1_waybel_0(sK1,k3_yellow_1(sK0)) )
      & ( ! [X5,X4] :
            ( r2_hidden(k2_xboole_0(X4,X5),sK1)
            | ~ r2_hidden(X5,sK1)
            | ~ r2_hidden(X4,sK1) )
        | v1_waybel_0(sK1,k3_yellow_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
      & v12_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ! [X1] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k2_xboole_0(X2,X3),X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k2_xboole_0(sK2,sK3),X1)
        & r2_hidden(sK3,X1)
        & r2_hidden(sK2,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f93,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( ~ r2_hidden(k2_xboole_0(X2,X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | ~ v1_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X4,X5] :
            ( r2_hidden(k2_xboole_0(X4,X5),X1)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | v1_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v12_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(rectify,[],[f92])).

fof(f92,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( ~ r2_hidden(k2_xboole_0(X2,X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | ~ v1_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X2,X3] :
            ( r2_hidden(k2_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) )
        | v1_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v12_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(flattening,[],[f91])).

fof(f91,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( ~ r2_hidden(k2_xboole_0(X2,X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | ~ v1_waybel_0(X1,k3_yellow_1(X0)) )
      & ( ! [X2,X3] :
            ( r2_hidden(k2_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) )
        | v1_waybel_0(X1,k3_yellow_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v12_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ? [X0,X1] :
      ( ( v1_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2,X3] :
            ( r2_hidden(k2_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v12_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ? [X0,X1] :
      ( ( v1_waybel_0(X1,k3_yellow_1(X0))
      <~> ! [X2,X3] :
            ( r2_hidden(k2_xboole_0(X2,X3),X1)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) ) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      & v12_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v12_waybel_0(X1,k3_yellow_1(X0)) )
       => ( v1_waybel_0(X1,k3_yellow_1(X0))
        <=> ! [X2,X3] :
              ( ( r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => r2_hidden(k2_xboole_0(X2,X3),X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
        & v12_waybel_0(X1,k3_yellow_1(X0)) )
     => ( v1_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X3,X1)
              & r2_hidden(X2,X1) )
           => r2_hidden(k2_xboole_0(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t12_waybel_7.p',t12_waybel_7)).

fof(f27300,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ v12_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27249,f110])).

fof(f110,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f96])).

fof(f27249,plain,
    ( r2_hidden(sK4(k3_yellow_1(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ v12_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(resolution,[],[f185,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              | ( ~ r2_hidden(k13_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
                & r2_hidden(sK5(X0,X1),X1)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f98,f100,f99])).

fof(f99,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(k13_lattice3(X0,sK4(X0,X1),X3),X1)
            & r2_hidden(X3,X1)
            & r2_hidden(sK4(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(k13_lattice3(X0,X2,sK5(X0,X1)),X1)
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(X2,X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(k13_lattice3(X0,X4,X5),X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                      | ~ r2_hidden(X3,X1)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v1_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0) )
         => ( v1_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t12_waybel_7.p',t40_waybel_0)).

fof(f185,plain,
    ( ~ v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f184])).

fof(f27299,plain,
    ( ~ spl9_1991
    | spl9_1998
    | spl9_1 ),
    inference(avatar_split_clause,[],[f27292,f184,f27297,f27258])).

fof(f27292,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27291,f123])).

fof(f27291,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27290,f127])).

fof(f27290,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27289,f109])).

fof(f27289,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ v12_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27248,f110])).

fof(f27248,plain,
    ( r2_hidden(sK5(k3_yellow_1(sK0),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ v12_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(resolution,[],[f185,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | r2_hidden(sK5(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f27288,plain,
    ( ~ spl9_1991
    | spl9_1996
    | spl9_1 ),
    inference(avatar_split_clause,[],[f27281,f184,f27286,f27258])).

fof(f27281,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27280,f123])).

fof(f27280,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27279,f127])).

fof(f27279,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27278,f109])).

fof(f27278,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v12_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27247,f110])).

fof(f27247,plain,
    ( m1_subset_1(sK4(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ v12_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(resolution,[],[f185,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f27277,plain,
    ( ~ spl9_1991
    | spl9_1994
    | spl9_1 ),
    inference(avatar_split_clause,[],[f27270,f184,f27275,f27258])).

fof(f27270,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27269,f123])).

fof(f27269,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27268,f127])).

fof(f27268,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27267,f109])).

fof(f27267,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ v12_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27246,f110])).

fof(f27246,plain,
    ( m1_subset_1(sK5(k3_yellow_1(sK0),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ v12_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(resolution,[],[f185,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f27266,plain,
    ( ~ spl9_1991
    | ~ spl9_1993
    | spl9_1 ),
    inference(avatar_split_clause,[],[f27253,f184,f27264,f27258])).

fof(f27253,plain,
    ( ~ r2_hidden(k13_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27252,f123])).

fof(f27252,plain,
    ( ~ r2_hidden(k13_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27251,f127])).

fof(f27251,plain,
    ( ~ r2_hidden(k13_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27250,f109])).

fof(f27250,plain,
    ( ~ r2_hidden(k13_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ v12_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f27245,f110])).

fof(f27245,plain,
    ( ~ r2_hidden(k13_lattice3(k3_yellow_1(sK0),sK4(k3_yellow_1(sK0),sK1),sK5(k3_yellow_1(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
    | ~ v12_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ l1_orders_2(k3_yellow_1(sK0))
    | ~ v1_lattice3(k3_yellow_1(sK0))
    | ~ v5_orders_2(k3_yellow_1(sK0))
    | ~ spl9_1 ),
    inference(resolution,[],[f185,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(X1,X0)
      | ~ r2_hidden(k13_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f27237,plain,
    ( ~ spl9_0
    | spl9_3
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f27236])).

fof(f27236,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f27235,f1438])).

fof(f1438,plain,
    ( m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_6 ),
    inference(resolution,[],[f1132,f110])).

fof(f1132,plain,
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
    file('/export/starexec/sandbox/benchmark/waybel_7__t12_waybel_7.p',t4_subset)).

fof(f205,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl9_6
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f27235,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_0
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f27234,f1413])).

fof(f1413,plain,
    ( m1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_4 ),
    inference(resolution,[],[f1128,f110])).

fof(f1128,plain,
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

fof(f27234,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_0
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f27233,f198])).

fof(f27233,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_0
    | ~ spl9_3
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f27222,f205])).

fof(f27222,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK3,sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(k3_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k3_yellow_1(sK0)))
    | ~ spl9_0
    | ~ spl9_3 ),
    inference(resolution,[],[f11999,f191])).

fof(f191,plain,
    ( ~ r2_hidden(k2_xboole_0(sK2,sK3),sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl9_3
  <=> ~ r2_hidden(k2_xboole_0(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f11999,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k2_xboole_0(X4,X5),sK1)
        | ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,u1_struct_0(k3_yellow_1(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(k3_yellow_1(sK0))) )
    | ~ spl9_0 ),
    inference(superposition,[],[f11909,f155])).

fof(f11909,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k13_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl9_0 ),
    inference(subsumption_resolution,[],[f11908,f110])).

fof(f11908,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(k13_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
        | ~ r2_hidden(X1,sK1) )
    | ~ spl9_0 ),
    inference(subsumption_resolution,[],[f11907,f182])).

fof(f182,plain,
    ( v1_waybel_0(sK1,k3_yellow_1(sK0))
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl9_0
  <=> v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f11907,plain,(
    ! [X0,X1] :
      ( ~ v1_waybel_0(sK1,k3_yellow_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(k13_lattice3(k3_yellow_1(sK0),X0,X1),sK1)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f8045,f109])).

fof(f8045,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v12_waybel_0(X1,k3_yellow_1(X2))
      | ~ v1_waybel_0(X1,k3_yellow_1(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(k13_lattice3(k3_yellow_1(X2),X0,X3),X1)
      | ~ r2_hidden(X3,X1) ) ),
    inference(subsumption_resolution,[],[f8044,f119])).

fof(f8044,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_waybel_0(X1,k3_yellow_1(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))
      | ~ v12_waybel_0(X1,k3_yellow_1(X2))
      | r2_hidden(k13_lattice3(k3_yellow_1(X2),X0,X3),X1)
      | ~ r2_hidden(X3,X1)
      | v2_struct_0(k3_yellow_1(X2)) ) ),
    inference(subsumption_resolution,[],[f8043,f127])).

fof(f8043,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_waybel_0(X1,k3_yellow_1(X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X2))))
      | ~ v12_waybel_0(X1,k3_yellow_1(X2))
      | ~ l1_orders_2(k3_yellow_1(X2))
      | r2_hidden(k13_lattice3(k3_yellow_1(X2),X0,X3),X1)
      | ~ r2_hidden(X3,X1)
      | v2_struct_0(k3_yellow_1(X2)) ) ),
    inference(resolution,[],[f5521,f125])).

fof(f5521,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v11_waybel_1(X3)
      | ~ r2_hidden(X2,X1)
      | ~ v1_waybel_0(X1,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v12_waybel_0(X1,X3)
      | ~ l1_orders_2(X3)
      | r2_hidden(k13_lattice3(X3,X2,X0),X1)
      | ~ r2_hidden(X0,X1)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f5520,f135])).

fof(f135,plain,(
    ! [X0] :
      ( v5_orders_2(X0)
      | ~ v11_waybel_1(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f5520,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ v1_waybel_0(X1,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v12_waybel_0(X1,X3)
      | ~ l1_orders_2(X3)
      | r2_hidden(k13_lattice3(X3,X2,X0),X1)
      | ~ v5_orders_2(X3)
      | ~ v11_waybel_1(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f5519])).

fof(f5519,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ v1_waybel_0(X1,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ v12_waybel_0(X1,X3)
      | ~ l1_orders_2(X3)
      | r2_hidden(k13_lattice3(X3,X2,X0),X1)
      | ~ v5_orders_2(X3)
      | ~ v11_waybel_1(X3)
      | v2_struct_0(X3)
      | ~ l1_orders_2(X3) ) ),
    inference(resolution,[],[f5178,f136])).

fof(f5178,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v1_lattice3(X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | r2_hidden(k13_lattice3(X0,X4,X5),X1)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f5177,f173])).

fof(f5177,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k13_lattice3(X0,X4,X5),X1)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f141,f173])).

fof(f141,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k13_lattice3(X0,X4,X5),X1)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v1_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f210,plain,
    ( spl9_0
    | spl9_8 ),
    inference(avatar_split_clause,[],[f111,f208,f181])).

fof(f111,plain,(
    ! [X4,X5] :
      ( r2_hidden(k2_xboole_0(X4,X5),sK1)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(X4,sK1)
      | v1_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f206,plain,
    ( ~ spl9_1
    | spl9_6 ),
    inference(avatar_split_clause,[],[f112,f204,f184])).

fof(f112,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

fof(f199,plain,
    ( ~ spl9_1
    | spl9_4 ),
    inference(avatar_split_clause,[],[f113,f197,f184])).

fof(f113,plain,
    ( r2_hidden(sK3,sK1)
    | ~ v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

fof(f192,plain,
    ( ~ spl9_1
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f114,f190,f184])).

fof(f114,plain,
    ( ~ r2_hidden(k2_xboole_0(sK2,sK3),sK1)
    | ~ v1_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f96])).
%------------------------------------------------------------------------------
