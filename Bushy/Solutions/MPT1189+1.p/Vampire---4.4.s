%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t161_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:18 EDT 2019

% Result     : Theorem 3.26s
% Output     : Refutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  265 ( 538 expanded)
%              Number of leaves         :   58 ( 205 expanded)
%              Depth                    :   15
%              Number of atoms          : 1067 (2974 expanded)
%              Number of equality atoms :   95 ( 365 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53655,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f182,f189,f196,f203,f210,f238,f281,f366,f382,f422,f486,f505,f541,f550,f710,f732,f2921,f3301,f3503,f14781,f27815,f27823,f37142,f37458,f37460,f37701,f37711,f52840,f52861,f53046,f53379,f53635,f53651])).

fof(f53651,plain,
    ( spl10_29
    | ~ spl10_104
    | spl10_349
    | ~ spl10_2058 ),
    inference(avatar_contradiction_clause,[],[f53650])).

fof(f53650,plain,
    ( $false
    | ~ spl10_29
    | ~ spl10_104
    | ~ spl10_349
    | ~ spl10_2058 ),
    inference(subsumption_resolution,[],[f53649,f280])).

fof(f280,plain,
    ( sK1 != sK2
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl10_29
  <=> sK1 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f53649,plain,
    ( sK1 = sK2
    | ~ spl10_104
    | ~ spl10_349
    | ~ spl10_2058 ),
    inference(subsumption_resolution,[],[f53644,f731])).

fof(f731,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl10_104 ),
    inference(avatar_component_clause,[],[f730])).

fof(f730,plain,
    ( spl10_104
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_104])])).

fof(f53644,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | sK1 = sK2
    | ~ spl10_349
    | ~ spl10_2058 ),
    inference(resolution,[],[f53634,f3485])).

fof(f3485,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl10_349 ),
    inference(avatar_component_clause,[],[f3484])).

fof(f3484,plain,
    ( spl10_349
  <=> ~ r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_349])])).

fof(f53634,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK1,X0)
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | sK1 = X0 )
    | ~ spl10_2058 ),
    inference(avatar_component_clause,[],[f53633])).

fof(f53633,plain,
    ( spl10_2058
  <=> ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2058])])).

fof(f53635,plain,
    ( spl10_2058
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_2054 ),
    inference(avatar_split_clause,[],[f53388,f53376,f236,f208,f53633])).

fof(f208,plain,
    ( spl10_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f236,plain,
    ( spl10_16
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f53376,plain,
    ( spl10_2054
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | sK1 = X0
        | r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2054])])).

fof(f53388,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,X0) )
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_2054 ),
    inference(subsumption_resolution,[],[f53387,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',t1_subset)).

fof(f53387,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_2054 ),
    inference(subsumption_resolution,[],[f53386,f209])).

fof(f209,plain,
    ( l1_orders_2(sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f208])).

fof(f53386,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl10_16
    | ~ spl10_2054 ),
    inference(subsumption_resolution,[],[f53380,f237])).

fof(f237,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f236])).

fof(f53380,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl10_2054 ),
    inference(resolution,[],[f53377,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
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
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',d9_orders_2)).

fof(f53377,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0))
        | sK1 = X0
        | ~ r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl10_2054 ),
    inference(avatar_component_clause,[],[f53376])).

fof(f53379,plain,
    ( spl10_2054
    | ~ spl10_26
    | ~ spl10_70
    | ~ spl10_1482 ),
    inference(avatar_split_clause,[],[f53211,f37456,f503,f270,f53376])).

fof(f270,plain,
    ( spl10_26
  <=> r9_orders_1(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f503,plain,
    ( spl10_70
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f37456,plain,
    ( spl10_1482
  <=> u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1482])])).

fof(f53211,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | sK1 = X0
        | r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0)) )
    | ~ spl10_26
    | ~ spl10_70
    | ~ spl10_1482 ),
    inference(forward_demodulation,[],[f53210,f37457])).

fof(f37457,plain,
    ( u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ spl10_1482 ),
    inference(avatar_component_clause,[],[f37456])).

fof(f53210,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(X0,k3_relat_1(u1_orders_2(sK0)))
        | r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0)) )
    | ~ spl10_26
    | ~ spl10_70 ),
    inference(subsumption_resolution,[],[f53208,f504])).

fof(f504,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_70 ),
    inference(avatar_component_clause,[],[f503])).

fof(f53208,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(X0,k3_relat_1(u1_orders_2(sK0)))
        | r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0))
        | ~ v1_relat_1(u1_orders_2(sK0)) )
    | ~ spl10_26 ),
    inference(resolution,[],[f271,f128])).

fof(f128,plain,(
    ! [X0,X3,X1] :
      ( ~ r9_orders_1(X0,X1)
      | X1 = X3
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X3),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r9_orders_1(X0,X1)
            | ( ~ r2_hidden(k4_tarski(X1,sK3(X0,X1)),X0)
              & sK3(X0,X1) != X1
              & r2_hidden(sK3(X0,X1),k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X3] :
                  ( r2_hidden(k4_tarski(X1,X3),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r9_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f101,f102])).

fof(f102,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(X1,sK3(X0,X1)),X0)
        & sK3(X0,X1) != X1
        & r2_hidden(sK3(X0,X1),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r9_orders_1(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X3] :
                  ( r2_hidden(k4_tarski(X1,X3),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r9_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r9_orders_1(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X2] :
                  ( r2_hidden(k4_tarski(X1,X2),X0)
                  | X1 = X2
                  | ~ r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r9_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r9_orders_1(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X2] :
                  ( r2_hidden(k4_tarski(X1,X2),X0)
                  | X1 = X2
                  | ~ r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r9_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r9_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( r2_hidden(k4_tarski(X1,X2),X0)
                | X1 = X2
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r9_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( r2_hidden(k4_tarski(X1,X2),X0)
                | X1 = X2
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r9_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( r2_hidden(X2,k3_relat_1(X0))
               => ( r2_hidden(k4_tarski(X1,X2),X0)
                  | X1 = X2 ) )
            & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',d14_orders_1)).

fof(f271,plain,
    ( r9_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f270])).

fof(f53046,plain,
    ( spl10_27
    | ~ spl10_56
    | ~ spl10_70
    | ~ spl10_1482
    | ~ spl10_2052 ),
    inference(avatar_contradiction_clause,[],[f53045])).

fof(f53045,plain,
    ( $false
    | ~ spl10_27
    | ~ spl10_56
    | ~ spl10_70
    | ~ spl10_1482
    | ~ spl10_2052 ),
    inference(subsumption_resolution,[],[f53044,f415])).

fof(f415,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f414])).

fof(f414,plain,
    ( spl10_56
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f53044,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_27
    | ~ spl10_70
    | ~ spl10_1482
    | ~ spl10_2052 ),
    inference(forward_demodulation,[],[f53043,f37457])).

fof(f53043,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ spl10_27
    | ~ spl10_70
    | ~ spl10_2052 ),
    inference(subsumption_resolution,[],[f53042,f504])).

fof(f53042,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_27
    | ~ spl10_2052 ),
    inference(subsumption_resolution,[],[f53034,f274])).

fof(f274,plain,
    ( ~ r9_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl10_27
  <=> ~ r9_orders_1(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f53034,plain,
    ( r9_orders_1(u1_orders_2(sK0),sK1)
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_2052 ),
    inference(resolution,[],[f52839,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,sK3(X0,X1)),X0)
      | r9_orders_1(X0,X1)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f52839,plain,
    ( r2_hidden(k4_tarski(sK1,sK3(u1_orders_2(sK0),sK1)),u1_orders_2(sK0))
    | ~ spl10_2052 ),
    inference(avatar_component_clause,[],[f52838])).

fof(f52838,plain,
    ( spl10_2052
  <=> r2_hidden(k4_tarski(sK1,sK3(u1_orders_2(sK0),sK1)),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2052])])).

fof(f52861,plain,
    ( spl10_27
    | ~ spl10_56
    | ~ spl10_70
    | ~ spl10_1482
    | ~ spl10_2050 ),
    inference(avatar_contradiction_clause,[],[f52860])).

fof(f52860,plain,
    ( $false
    | ~ spl10_27
    | ~ spl10_56
    | ~ spl10_70
    | ~ spl10_1482
    | ~ spl10_2050 ),
    inference(subsumption_resolution,[],[f52859,f415])).

fof(f52859,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_27
    | ~ spl10_70
    | ~ spl10_1482
    | ~ spl10_2050 ),
    inference(forward_demodulation,[],[f52858,f37457])).

fof(f52858,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ spl10_27
    | ~ spl10_70
    | ~ spl10_2050 ),
    inference(subsumption_resolution,[],[f52857,f504])).

fof(f52857,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_27
    | ~ spl10_2050 ),
    inference(subsumption_resolution,[],[f52850,f274])).

fof(f52850,plain,
    ( r9_orders_1(u1_orders_2(sK0),sK1)
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_2050 ),
    inference(trivial_inequality_removal,[],[f52849])).

fof(f52849,plain,
    ( sK1 != sK1
    | r9_orders_1(u1_orders_2(sK0),sK1)
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_2050 ),
    inference(superposition,[],[f130,f52833])).

fof(f52833,plain,
    ( sK1 = sK3(u1_orders_2(sK0),sK1)
    | ~ spl10_2050 ),
    inference(avatar_component_clause,[],[f52832])).

fof(f52832,plain,
    ( spl10_2050
  <=> sK1 = sK3(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2050])])).

fof(f130,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X1
      | r9_orders_1(X0,X1)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f52840,plain,
    ( spl10_2050
    | spl10_2052
    | ~ spl10_102
    | ~ spl10_1486 ),
    inference(avatar_split_clause,[],[f37737,f37709,f708,f52838,f52832])).

fof(f708,plain,
    ( spl10_102
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0))
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_102])])).

fof(f37709,plain,
    ( spl10_1486
  <=> m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1486])])).

fof(f37737,plain,
    ( r2_hidden(k4_tarski(sK1,sK3(u1_orders_2(sK0),sK1)),u1_orders_2(sK0))
    | sK1 = sK3(u1_orders_2(sK0),sK1)
    | ~ spl10_102
    | ~ spl10_1486 ),
    inference(resolution,[],[f37710,f709])).

fof(f709,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0))
        | sK1 = X0 )
    | ~ spl10_102 ),
    inference(avatar_component_clause,[],[f708])).

fof(f37710,plain,
    ( m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl10_1486 ),
    inference(avatar_component_clause,[],[f37709])).

fof(f37711,plain,
    ( spl10_1486
    | ~ spl10_1484 ),
    inference(avatar_split_clause,[],[f37702,f37699,f37709])).

fof(f37699,plain,
    ( spl10_1484
  <=> r2_hidden(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1484])])).

fof(f37702,plain,
    ( m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl10_1484 ),
    inference(resolution,[],[f37700,f150])).

fof(f37700,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl10_1484 ),
    inference(avatar_component_clause,[],[f37699])).

fof(f37701,plain,
    ( spl10_1484
    | ~ spl10_874
    | ~ spl10_1482 ),
    inference(avatar_split_clause,[],[f37694,f37456,f14779,f37699])).

fof(f14779,plain,
    ( spl10_874
  <=> r2_hidden(sK3(u1_orders_2(sK0),sK1),k3_relat_1(u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_874])])).

fof(f37694,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl10_874
    | ~ spl10_1482 ),
    inference(forward_demodulation,[],[f14780,f37457])).

fof(f14780,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),sK1),k3_relat_1(u1_orders_2(sK0)))
    | ~ spl10_874 ),
    inference(avatar_component_clause,[],[f14779])).

fof(f37460,plain,
    ( ~ spl10_56
    | ~ spl10_68
    | spl10_333
    | ~ spl10_1312
    | ~ spl10_1464 ),
    inference(avatar_contradiction_clause,[],[f37459])).

fof(f37459,plain,
    ( $false
    | ~ spl10_56
    | ~ spl10_68
    | ~ spl10_333
    | ~ spl10_1312
    | ~ spl10_1464 ),
    inference(subsumption_resolution,[],[f37425,f415])).

fof(f37425,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_68
    | ~ spl10_333
    | ~ spl10_1312
    | ~ spl10_1464 ),
    inference(backward_demodulation,[],[f37423,f3319])).

fof(f3319,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ spl10_333 ),
    inference(avatar_component_clause,[],[f3318])).

fof(f3318,plain,
    ( spl10_333
  <=> ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_333])])).

fof(f37423,plain,
    ( u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ spl10_68
    | ~ spl10_1312
    | ~ spl10_1464 ),
    inference(subsumption_resolution,[],[f37422,f27794])).

fof(f27794,plain,
    ( v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl10_1312 ),
    inference(avatar_component_clause,[],[f27793])).

fof(f27793,plain,
    ( spl10_1312
  <=> v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1312])])).

fof(f37422,plain,
    ( ~ v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ spl10_68
    | ~ spl10_1464 ),
    inference(resolution,[],[f37141,f485])).

fof(f485,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_68 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl10_68
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).

fof(f37141,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(u1_orders_2(sK0),X0)
        | k3_relat_1(u1_orders_2(sK0)) = X0 )
    | ~ spl10_1464 ),
    inference(avatar_component_clause,[],[f37140])).

fof(f37140,plain,
    ( spl10_1464
  <=> ! [X0] :
        ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(u1_orders_2(sK0),X0)
        | k3_relat_1(u1_orders_2(sK0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1464])])).

fof(f37458,plain,
    ( spl10_1482
    | ~ spl10_68
    | ~ spl10_1312
    | ~ spl10_1464 ),
    inference(avatar_split_clause,[],[f37423,f37140,f27793,f484,f37456])).

fof(f37142,plain,
    ( spl10_1464
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f6610,f208,f201,f194,f187,f37140])).

fof(f187,plain,
    ( spl10_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f194,plain,
    ( spl10_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f201,plain,
    ( spl10_6
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f6610,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(u1_orders_2(sK0),X0)
        | k3_relat_1(u1_orders_2(sK0)) = X0 )
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f6609,f188])).

fof(f188,plain,
    ( v3_orders_2(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f187])).

fof(f6609,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(u1_orders_2(sK0),X0)
        | k3_relat_1(u1_orders_2(sK0)) = X0
        | ~ v3_orders_2(sK0) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f6608,f195])).

fof(f195,plain,
    ( v4_orders_2(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f194])).

fof(f6608,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(u1_orders_2(sK0),X0)
        | ~ v4_orders_2(sK0)
        | k3_relat_1(u1_orders_2(sK0)) = X0
        | ~ v3_orders_2(sK0) )
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f6607,f209])).

fof(f6607,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_partfun1(u1_orders_2(sK0),X0)
        | ~ l1_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | k3_relat_1(u1_orders_2(sK0)) = X0
        | ~ v3_orders_2(sK0) )
    | ~ spl10_6 ),
    inference(resolution,[],[f988,f202])).

fof(f202,plain,
    ( v5_orders_2(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f201])).

fof(f988,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(u1_orders_2(X0),X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | k3_relat_1(u1_orders_2(X0)) = X1
      | ~ v3_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f987,f134])).

fof(f134,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
       => v2_orders_2(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',cc1_orders_2)).

fof(f987,plain,(
    ! [X0,X1] :
      ( k3_relat_1(u1_orders_2(X0)) = X1
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(u1_orders_2(X0),X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f986])).

fof(f986,plain,(
    ! [X0,X1] :
      ( k3_relat_1(u1_orders_2(X0)) = X1
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(u1_orders_2(X0),X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(resolution,[],[f590,f145])).

fof(f145,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => v1_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',fc3_orders_2)).

fof(f590,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_2(u1_orders_2(X0))
      | k3_relat_1(u1_orders_2(X0)) = X1
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_partfun1(u1_orders_2(X0),X1)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f589])).

fof(f589,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(u1_orders_2(X0),X1)
      | k3_relat_1(u1_orders_2(X0)) = X1
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(resolution,[],[f427,f142])).

fof(f142,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v2_orders_2(X0) )
     => v4_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',fc4_orders_2)).

fof(f427,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_2(u1_orders_2(X0))
      | ~ v1_partfun1(u1_orders_2(X0),X1)
      | k3_relat_1(u1_orders_2(X0)) = X1
      | ~ m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
      | ~ v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(resolution,[],[f152,f143])).

fof(f143,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v2_orders_2(X0) )
     => v8_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',fc5_orders_2)).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ v8_relat_2(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | k3_relat_1(X1) = X0
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v4_relat_2(X1)
        & v1_relat_2(X1) )
     => k3_relat_1(X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',t100_orders_1)).

fof(f27823,plain,
    ( ~ spl10_2
    | ~ spl10_8
    | spl10_1317 ),
    inference(avatar_contradiction_clause,[],[f27822])).

fof(f27822,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_8
    | ~ spl10_1317 ),
    inference(subsumption_resolution,[],[f27821,f209])).

fof(f27821,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_2
    | ~ spl10_1317 ),
    inference(subsumption_resolution,[],[f27819,f188])).

fof(f27819,plain,
    ( ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl10_1317 ),
    inference(resolution,[],[f27814,f134])).

fof(f27814,plain,
    ( ~ v2_orders_2(sK0)
    | ~ spl10_1317 ),
    inference(avatar_component_clause,[],[f27813])).

fof(f27813,plain,
    ( spl10_1317
  <=> ~ v2_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1317])])).

fof(f27815,plain,
    ( ~ spl10_1317
    | ~ spl10_8
    | spl10_1313 ),
    inference(avatar_split_clause,[],[f27807,f27796,f208,f27813])).

fof(f27796,plain,
    ( spl10_1313
  <=> ~ v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1313])])).

fof(f27807,plain,
    ( ~ v2_orders_2(sK0)
    | ~ spl10_8
    | ~ spl10_1313 ),
    inference(subsumption_resolution,[],[f27806,f209])).

fof(f27806,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_orders_2(sK0)
    | ~ spl10_1313 ),
    inference(resolution,[],[f27797,f144])).

fof(f144,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_orders_2(X0) )
     => v1_partfun1(u1_orders_2(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',fc2_orders_2)).

fof(f27797,plain,
    ( ~ v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ spl10_1313 ),
    inference(avatar_component_clause,[],[f27796])).

fof(f14781,plain,
    ( spl10_874
    | spl10_27
    | ~ spl10_298
    | ~ spl10_332 ),
    inference(avatar_split_clause,[],[f14772,f3321,f2919,f273,f14779])).

fof(f2919,plain,
    ( spl10_298
  <=> ! [X0] :
        ( r2_hidden(sK3(u1_orders_2(sK0),X0),k3_relat_1(u1_orders_2(sK0)))
        | ~ r2_hidden(X0,k3_relat_1(u1_orders_2(sK0)))
        | r9_orders_1(u1_orders_2(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_298])])).

fof(f3321,plain,
    ( spl10_332
  <=> r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_332])])).

fof(f14772,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),sK1),k3_relat_1(u1_orders_2(sK0)))
    | ~ spl10_27
    | ~ spl10_298
    | ~ spl10_332 ),
    inference(subsumption_resolution,[],[f14769,f274])).

fof(f14769,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),sK1),k3_relat_1(u1_orders_2(sK0)))
    | r9_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl10_298
    | ~ spl10_332 ),
    inference(resolution,[],[f2920,f3322])).

fof(f3322,plain,
    ( r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ spl10_332 ),
    inference(avatar_component_clause,[],[f3321])).

fof(f2920,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(u1_orders_2(sK0)))
        | r2_hidden(sK3(u1_orders_2(sK0),X0),k3_relat_1(u1_orders_2(sK0)))
        | r9_orders_1(u1_orders_2(sK0),X0) )
    | ~ spl10_298 ),
    inference(avatar_component_clause,[],[f2919])).

fof(f3503,plain,
    ( spl10_330
    | ~ spl10_8
    | ~ spl10_16
    | spl10_29
    | ~ spl10_50
    | ~ spl10_348 ),
    inference(avatar_split_clause,[],[f3502,f3487,f380,f279,f236,f208,f3296])).

fof(f3296,plain,
    ( spl10_330
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_330])])).

fof(f380,plain,
    ( spl10_50
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f3487,plain,
    ( spl10_348
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_348])])).

fof(f3502,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_29
    | ~ spl10_50
    | ~ spl10_348 ),
    inference(subsumption_resolution,[],[f3501,f209])).

fof(f3501,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl10_16
    | ~ spl10_29
    | ~ spl10_50
    | ~ spl10_348 ),
    inference(subsumption_resolution,[],[f3500,f237])).

fof(f3500,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_29
    | ~ spl10_50
    | ~ spl10_348 ),
    inference(subsumption_resolution,[],[f3494,f381])).

fof(f381,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f380])).

fof(f3494,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_29
    | ~ spl10_348 ),
    inference(subsumption_resolution,[],[f3491,f280])).

fof(f3491,plain,
    ( sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl10_348 ),
    inference(resolution,[],[f3488,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | X1 = X2
      | r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',d10_orders_2)).

fof(f3488,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl10_348 ),
    inference(avatar_component_clause,[],[f3487])).

fof(f3301,plain,
    ( ~ spl10_331
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f3286,f270,f3299])).

fof(f3299,plain,
    ( spl10_331
  <=> ~ r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_331])])).

fof(f3286,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f124,f271])).

fof(f124,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ r9_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,
    ( ( ( ~ r2_orders_2(sK0,sK1,sK2)
        & sK1 != sK2
        & m1_subset_1(sK2,u1_struct_0(sK0)) )
      | ~ r9_orders_1(u1_orders_2(sK0),sK1) )
    & ( ! [X3] :
          ( r2_orders_2(sK0,sK1,X3)
          | sK1 = X3
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      | r9_orders_1(u1_orders_2(sK0),sK1) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f94,f97,f96,f95])).

fof(f95,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ~ r2_orders_2(X0,X1,X2)
                  & X1 != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r9_orders_1(u1_orders_2(X0),X1) )
            & ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | X1 = X3
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | r9_orders_1(u1_orders_2(X0),X1) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(sK0,X1,X2)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ r9_orders_1(u1_orders_2(sK0),X1) )
          & ( ! [X3] :
                ( r2_orders_2(sK0,X1,X3)
                | X1 = X3
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            | r9_orders_1(u1_orders_2(sK0),X1) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f96,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r9_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X3] :
                ( r2_orders_2(X0,X1,X3)
                | X1 = X3
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | r9_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ? [X2] :
              ( ~ r2_orders_2(X0,sK1,X2)
              & sK1 != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ r9_orders_1(u1_orders_2(X0),sK1) )
        & ( ! [X3] :
              ( r2_orders_2(X0,sK1,X3)
              | sK1 = X3
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | r9_orders_1(u1_orders_2(X0),sK1) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_orders_2(X0,X1,X2)
          & X1 != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X1,sK2)
        & sK2 != X1
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r9_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X3] :
                ( r2_orders_2(X0,X1,X3)
                | X1 = X3
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | r9_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f93])).

fof(f93,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r9_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X2] :
                ( r2_orders_2(X0,X1,X2)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | r9_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                & X1 != X2
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r9_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X2] :
                ( r2_orders_2(X0,X1,X2)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | r9_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r9_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( r2_orders_2(X0,X1,X2)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r9_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( r2_orders_2(X0,X1,X2)
                | X1 = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r9_orders_1(u1_orders_2(X0),X1)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( X1 != X2
                   => r2_orders_2(X0,X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r9_orders_1(u1_orders_2(X0),X1)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( X1 != X2
                 => r2_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',t161_orders_2)).

fof(f2921,plain,
    ( spl10_298
    | ~ spl10_70 ),
    inference(avatar_split_clause,[],[f513,f503,f2919])).

fof(f513,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(u1_orders_2(sK0),X0),k3_relat_1(u1_orders_2(sK0)))
        | ~ r2_hidden(X0,k3_relat_1(u1_orders_2(sK0)))
        | r9_orders_1(u1_orders_2(sK0),X0) )
    | ~ spl10_70 ),
    inference(resolution,[],[f504,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),k3_relat_1(X0))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | r9_orders_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f732,plain,
    ( spl10_104
    | ~ spl10_50
    | spl10_59 ),
    inference(avatar_split_clause,[],[f725,f417,f380,f730])).

fof(f417,plain,
    ( spl10_59
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).

fof(f725,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl10_50
    | ~ spl10_59 ),
    inference(subsumption_resolution,[],[f720,f418])).

fof(f418,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_59 ),
    inference(avatar_component_clause,[],[f417])).

fof(f720,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl10_50 ),
    inference(resolution,[],[f381,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',t2_subset)).

fof(f710,plain,
    ( spl10_102
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f581,f364,f236,f208,f708])).

fof(f364,plain,
    ( spl10_46
  <=> ! [X3] :
        ( r2_orders_2(sK0,sK1,X3)
        | sK1 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f581,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0))
        | sK1 = X0 )
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_46 ),
    inference(subsumption_resolution,[],[f580,f209])).

fof(f580,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0))
        | sK1 = X0 )
    | ~ spl10_16
    | ~ spl10_46 ),
    inference(subsumption_resolution,[],[f579,f237])).

fof(f579,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0))
        | sK1 = X0 )
    | ~ spl10_46 ),
    inference(duplicate_literal_removal,[],[f578])).

fof(f578,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0))
        | sK1 = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_46 ),
    inference(resolution,[],[f442,f365])).

fof(f365,plain,
    ( ! [X3] :
        ( r2_orders_2(sK0,sK1,X3)
        | sK1 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f364])).

fof(f442,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(X2)) ) ),
    inference(duplicate_literal_removal,[],[f441])).

fof(f441,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ l1_orders_2(X2)
      | ~ r2_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f135,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f106])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f550,plain,
    ( ~ spl10_8
    | spl10_79 ),
    inference(avatar_contradiction_clause,[],[f549])).

fof(f549,plain,
    ( $false
    | ~ spl10_8
    | ~ spl10_79 ),
    inference(subsumption_resolution,[],[f547,f209])).

fof(f547,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_79 ),
    inference(resolution,[],[f540,f132])).

fof(f132,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',dt_l1_orders_2)).

fof(f540,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl10_79 ),
    inference(avatar_component_clause,[],[f539])).

fof(f539,plain,
    ( spl10_79
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f541,plain,
    ( ~ spl10_79
    | spl10_1
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f534,f420,f180,f539])).

fof(f180,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f420,plain,
    ( spl10_58
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f534,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_58 ),
    inference(subsumption_resolution,[],[f530,f181])).

fof(f181,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f180])).

fof(f530,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_58 ),
    inference(resolution,[],[f421,f141])).

fof(f141,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',fc2_struct_0)).

fof(f421,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f420])).

fof(f505,plain,
    ( spl10_70
    | ~ spl10_68 ),
    inference(avatar_split_clause,[],[f494,f484,f503])).

fof(f494,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_68 ),
    inference(resolution,[],[f485,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',cc1_relset_1)).

fof(f486,plain,
    ( spl10_68
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f333,f208,f484])).

fof(f333,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_8 ),
    inference(resolution,[],[f133,f209])).

fof(f133,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t161_orders_2.p',dt_u1_orders_2)).

fof(f422,plain,
    ( spl10_56
    | spl10_58
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f303,f236,f420,f414])).

fof(f303,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_16 ),
    inference(resolution,[],[f151,f237])).

fof(f382,plain,
    ( spl10_50
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f374,f270,f380])).

fof(f374,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f122,f271])).

fof(f122,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r9_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f98])).

fof(f366,plain,
    ( spl10_46
    | spl10_27 ),
    inference(avatar_split_clause,[],[f355,f273,f364])).

fof(f355,plain,
    ( ! [X3] :
        ( r2_orders_2(sK0,sK1,X3)
        | sK1 = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl10_27 ),
    inference(subsumption_resolution,[],[f121,f274])).

fof(f121,plain,(
    ! [X3] :
      ( r2_orders_2(sK0,sK1,X3)
      | sK1 = X3
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r9_orders_1(u1_orders_2(sK0),sK1) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f281,plain,
    ( ~ spl10_27
    | ~ spl10_29 ),
    inference(avatar_split_clause,[],[f123,f279,f273])).

fof(f123,plain,
    ( sK1 != sK2
    | ~ r9_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f98])).

fof(f238,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f120,f236])).

fof(f120,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f98])).

fof(f210,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f119,f208])).

fof(f119,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f203,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f118,f201])).

fof(f118,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f196,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f117,f194])).

fof(f117,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f189,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f116,f187])).

fof(f116,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f98])).

fof(f182,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f115,f180])).

fof(f115,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f98])).
%------------------------------------------------------------------------------
