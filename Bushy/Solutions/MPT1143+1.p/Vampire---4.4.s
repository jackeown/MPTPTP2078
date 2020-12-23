%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t35_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:19 EDT 2019

% Result     : Theorem 3.29s
% Output     : Refutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 291 expanded)
%              Number of leaves         :   45 ( 119 expanded)
%              Depth                    :   12
%              Number of atoms          :  592 (1083 expanded)
%              Number of equality atoms :   47 (  85 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77458,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f136,f143,f150,f178,f280,f340,f361,f387,f446,f466,f494,f510,f518,f1537,f1548,f2336,f2643,f8454,f12397,f12410,f33466,f72118,f77192,f77221,f77457])).

fof(f77457,plain,
    ( ~ spl10_54
    | spl10_1183
    | ~ spl10_2330
    | ~ spl10_3660
    | ~ spl10_3662 ),
    inference(avatar_contradiction_clause,[],[f77456])).

fof(f77456,plain,
    ( $false
    | ~ spl10_54
    | ~ spl10_1183
    | ~ spl10_2330
    | ~ spl10_3660
    | ~ spl10_3662 ),
    inference(subsumption_resolution,[],[f77455,f33453])).

fof(f33453,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | ~ spl10_2330 ),
    inference(avatar_component_clause,[],[f33452])).

fof(f33452,plain,
    ( spl10_2330
  <=> r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2330])])).

fof(f77455,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | ~ spl10_54
    | ~ spl10_1183
    | ~ spl10_3660
    | ~ spl10_3662 ),
    inference(forward_demodulation,[],[f77454,f77191])).

fof(f77191,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k1_tarski(sK1))
    | ~ spl10_3660 ),
    inference(avatar_component_clause,[],[f77190])).

fof(f77190,plain,
    ( spl10_3660
  <=> sK1 = sK3(u1_orders_2(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3660])])).

fof(f77454,plain,
    ( ~ r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),k1_tarski(sK1)),sK1),u1_orders_2(sK0))
    | ~ spl10_54
    | ~ spl10_1183
    | ~ spl10_3662 ),
    inference(subsumption_resolution,[],[f77453,f386])).

fof(f386,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl10_54
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f77453,plain,
    ( ~ r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),k1_tarski(sK1)),sK1),u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_1183
    | ~ spl10_3662 ),
    inference(subsumption_resolution,[],[f77447,f15302])).

fof(f15302,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),k1_tarski(sK1))
    | ~ spl10_1183 ),
    inference(avatar_component_clause,[],[f15301])).

fof(f15301,plain,
    ( spl10_1183
  <=> ~ r7_relat_2(u1_orders_2(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1183])])).

fof(f77447,plain,
    ( ~ r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),k1_tarski(sK1)),sK1),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k1_tarski(sK1))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_3662 ),
    inference(superposition,[],[f96,f77220])).

fof(f77220,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k1_tarski(sK1))
    | ~ spl10_3662 ),
    inference(avatar_component_clause,[],[f77219])).

fof(f77219,plain,
    ( spl10_3662
  <=> sK1 = sK4(u1_orders_2(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3662])])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r7_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
              & r2_hidden(sK4(X0,X1),X1)
              & r2_hidden(sK3(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f68,f69])).

fof(f69,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X3,X2),X0)
                | r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',d7_relat_2)).

fof(f77221,plain,
    ( spl10_3662
    | ~ spl10_948
    | spl10_1183 ),
    inference(avatar_split_clause,[],[f72123,f15301,f12330,f77219])).

fof(f12330,plain,
    ( spl10_948
  <=> ! [X5] :
        ( r7_relat_2(u1_orders_2(sK0),k1_tarski(X5))
        | sK4(u1_orders_2(sK0),k1_tarski(X5)) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_948])])).

fof(f72123,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k1_tarski(sK1))
    | ~ spl10_948
    | ~ spl10_1183 ),
    inference(resolution,[],[f15302,f12331])).

fof(f12331,plain,
    ( ! [X5] :
        ( r7_relat_2(u1_orders_2(sK0),k1_tarski(X5))
        | sK4(u1_orders_2(sK0),k1_tarski(X5)) = X5 )
    | ~ spl10_948 ),
    inference(avatar_component_clause,[],[f12330])).

fof(f77192,plain,
    ( spl10_3660
    | ~ spl10_950
    | spl10_1183 ),
    inference(avatar_split_clause,[],[f72122,f15301,f12368,f77190])).

fof(f12368,plain,
    ( spl10_950
  <=> ! [X5] :
        ( r7_relat_2(u1_orders_2(sK0),k1_tarski(X5))
        | sK3(u1_orders_2(sK0),k1_tarski(X5)) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_950])])).

fof(f72122,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k1_tarski(sK1))
    | ~ spl10_950
    | ~ spl10_1183 ),
    inference(resolution,[],[f15302,f12369])).

fof(f12369,plain,
    ( ! [X5] :
        ( r7_relat_2(u1_orders_2(sK0),k1_tarski(X5))
        | sK3(u1_orders_2(sK0),k1_tarski(X5)) = X5 )
    | ~ spl10_950 ),
    inference(avatar_component_clause,[],[f12368])).

fof(f72118,plain,
    ( ~ spl10_4
    | spl10_65
    | ~ spl10_66
    | ~ spl10_1182 ),
    inference(avatar_contradiction_clause,[],[f72117])).

fof(f72117,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_65
    | ~ spl10_66
    | ~ spl10_1182 ),
    inference(subsumption_resolution,[],[f72116,f149])).

fof(f149,plain,
    ( l1_orders_2(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl10_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f72116,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_65
    | ~ spl10_66
    | ~ spl10_1182 ),
    inference(subsumption_resolution,[],[f72115,f493])).

fof(f493,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_66 ),
    inference(avatar_component_clause,[],[f492])).

fof(f492,plain,
    ( spl10_66
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f72115,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl10_65
    | ~ spl10_1182 ),
    inference(subsumption_resolution,[],[f72112,f465])).

fof(f465,plain,
    ( ~ v6_orders_2(k1_tarski(sK1),sK0)
    | ~ spl10_65 ),
    inference(avatar_component_clause,[],[f464])).

fof(f464,plain,
    ( spl10_65
  <=> ~ v6_orders_2(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).

fof(f72112,plain,
    ( v6_orders_2(k1_tarski(sK1),sK0)
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl10_1182 ),
    inference(resolution,[],[f15305,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r7_relat_2(u1_orders_2(X0),X1)
      | v6_orders_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',d11_orders_2)).

fof(f15305,plain,
    ( r7_relat_2(u1_orders_2(sK0),k1_tarski(sK1))
    | ~ spl10_1182 ),
    inference(avatar_component_clause,[],[f15304])).

fof(f15304,plain,
    ( spl10_1182
  <=> r7_relat_2(u1_orders_2(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1182])])).

fof(f33466,plain,
    ( ~ spl10_42
    | ~ spl10_308
    | spl10_2331 ),
    inference(avatar_contradiction_clause,[],[f33465])).

fof(f33465,plain,
    ( $false
    | ~ spl10_42
    | ~ spl10_308
    | ~ spl10_2331 ),
    inference(subsumption_resolution,[],[f33463,f333])).

fof(f333,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl10_42
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f33463,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_308
    | ~ spl10_2331 ),
    inference(resolution,[],[f33456,f2642])).

fof(f2642,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0))
        | ~ r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl10_308 ),
    inference(avatar_component_clause,[],[f2641])).

fof(f2641,plain,
    ( spl10_308
  <=> ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_308])])).

fof(f33456,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | ~ spl10_2331 ),
    inference(avatar_component_clause,[],[f33455])).

fof(f33455,plain,
    ( spl10_2331
  <=> ~ r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2331])])).

fof(f12410,plain,
    ( spl10_950
    | ~ spl10_184 ),
    inference(avatar_split_clause,[],[f2099,f1546,f12368])).

fof(f1546,plain,
    ( spl10_184
  <=> ! [X3] :
        ( r2_hidden(sK3(u1_orders_2(sK0),X3),X3)
        | r7_relat_2(u1_orders_2(sK0),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_184])])).

fof(f2099,plain,
    ( ! [X5] :
        ( r7_relat_2(u1_orders_2(sK0),k1_tarski(X5))
        | sK3(u1_orders_2(sK0),k1_tarski(X5)) = X5 )
    | ~ spl10_184 ),
    inference(resolution,[],[f1547,f127])).

fof(f127,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f76,f77])).

fof(f77,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',d1_tarski)).

fof(f1547,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(u1_orders_2(sK0),X3),X3)
        | r7_relat_2(u1_orders_2(sK0),X3) )
    | ~ spl10_184 ),
    inference(avatar_component_clause,[],[f1546])).

fof(f12397,plain,
    ( spl10_948
    | ~ spl10_180 ),
    inference(avatar_split_clause,[],[f2083,f1535,f12330])).

fof(f1535,plain,
    ( spl10_180
  <=> ! [X2] :
        ( r2_hidden(sK4(u1_orders_2(sK0),X2),X2)
        | r7_relat_2(u1_orders_2(sK0),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_180])])).

fof(f2083,plain,
    ( ! [X5] :
        ( r7_relat_2(u1_orders_2(sK0),k1_tarski(X5))
        | sK4(u1_orders_2(sK0),k1_tarski(X5)) = X5 )
    | ~ spl10_180 ),
    inference(resolution,[],[f1536,f127])).

fof(f1536,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(u1_orders_2(sK0),X2),X2)
        | r7_relat_2(u1_orders_2(sK0),X2) )
    | ~ spl10_180 ),
    inference(avatar_component_clause,[],[f1535])).

fof(f8454,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) != k1_tarski(sK1)
    | m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_axiom,[])).

fof(f2643,plain,
    ( spl10_308
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_272 ),
    inference(avatar_split_clause,[],[f2364,f2318,f148,f141,f2641])).

fof(f141,plain,
    ( spl10_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f2318,plain,
    ( spl10_272
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_relat_2(u1_orders_2(sK0),X1)
        | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_272])])).

fof(f2364,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0)) )
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_272 ),
    inference(subsumption_resolution,[],[f2363,f149])).

fof(f2363,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl10_2
    | ~ spl10_272 ),
    inference(subsumption_resolution,[],[f2361,f142])).

fof(f142,plain,
    ( v3_orders_2(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f141])).

fof(f2361,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(sK0))
        | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0))
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0) )
    | ~ spl10_272 ),
    inference(resolution,[],[f2319,f100])).

fof(f100,plain,(
    ! [X0] :
      ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ( ( v3_orders_2(X0)
          | ~ r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r1_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v3_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
      <=> r1_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',d4_orders_2)).

fof(f2319,plain,
    ( ! [X0,X1] :
        ( ~ r1_relat_2(u1_orders_2(sK0),X1)
        | ~ r2_hidden(X0,X1)
        | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0)) )
    | ~ spl10_272 ),
    inference(avatar_component_clause,[],[f2318])).

fof(f2336,plain,
    ( spl10_272
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f1972,f385,f2318])).

fof(f1972,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_relat_2(u1_orders_2(sK0),X1)
        | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0)) )
    | ~ spl10_54 ),
    inference(resolution,[],[f386,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,X1)
      | ~ r1_relat_2(X0,X1)
      | r2_hidden(k4_tarski(X3,X3),X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK2(X0,X1)),X0)
              & r2_hidden(sK2(X0,X1),X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f64,f65])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK2(X0,X1)),X0)
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X3] :
                ( r2_hidden(k4_tarski(X3,X3),X0)
                | ~ r2_hidden(X3,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_relat_2(X0,X1)
            | ? [X2] :
                ( ~ r2_hidden(k4_tarski(X2,X2),X0)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2] :
                ( r2_hidden(k4_tarski(X2,X2),X0)
                | ~ r2_hidden(X2,X1) )
            | ~ r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(k4_tarski(X2,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_relat_2(X0,X1)
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
             => r2_hidden(k4_tarski(X2,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',d1_relat_2)).

fof(f1548,plain,
    ( spl10_184
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f392,f385,f1546])).

fof(f392,plain,
    ( ! [X3] :
        ( r2_hidden(sK3(u1_orders_2(sK0),X3),X3)
        | r7_relat_2(u1_orders_2(sK0),X3) )
    | ~ spl10_54 ),
    inference(resolution,[],[f386,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),X1)
      | r7_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f1537,plain,
    ( spl10_180
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f391,f385,f1535])).

fof(f391,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(u1_orders_2(sK0),X2),X2)
        | r7_relat_2(u1_orders_2(sK0),X2) )
    | ~ spl10_54 ),
    inference(resolution,[],[f386,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | r7_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f518,plain,
    ( ~ spl10_4
    | spl10_69 ),
    inference(avatar_contradiction_clause,[],[f517])).

fof(f517,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_69 ),
    inference(subsumption_resolution,[],[f515,f149])).

fof(f515,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_69 ),
    inference(resolution,[],[f509,f98])).

fof(f98,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',dt_l1_orders_2)).

fof(f509,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl10_69 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl10_69
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f510,plain,
    ( ~ spl10_69
    | spl10_1
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f500,f338,f134,f508])).

fof(f134,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f338,plain,
    ( spl10_44
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f500,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl10_1
    | ~ spl10_44 ),
    inference(subsumption_resolution,[],[f495,f135])).

fof(f135,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f495,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_44 ),
    inference(resolution,[],[f339,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',fc2_struct_0)).

fof(f339,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f338])).

fof(f494,plain,
    ( spl10_44
    | spl10_66
    | ~ spl10_12
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f478,f444,f176,f492,f338])).

fof(f176,plain,
    ( spl10_12
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f444,plain,
    ( spl10_62
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f478,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_12
    | ~ spl10_62 ),
    inference(forward_demodulation,[],[f252,f445])).

fof(f445,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl10_62 ),
    inference(avatar_component_clause,[],[f444])).

fof(f252,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_12 ),
    inference(resolution,[],[f111,f177])).

fof(f177,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f176])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',dt_k6_domain_1)).

fof(f466,plain,
    ( ~ spl10_65
    | spl10_31
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f455,f444,f272,f464])).

fof(f272,plain,
    ( spl10_31
  <=> ~ v6_orders_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f455,plain,
    ( ~ v6_orders_2(k1_tarski(sK1),sK0)
    | ~ spl10_31
    | ~ spl10_62 ),
    inference(backward_demodulation,[],[f445,f273])).

fof(f273,plain,
    ( ~ v6_orders_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f272])).

fof(f446,plain,
    ( spl10_44
    | spl10_62
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f247,f176,f444,f338])).

fof(f247,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_12 ),
    inference(resolution,[],[f110,f177])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',redefinition_k6_domain_1)).

fof(f387,plain,
    ( spl10_54
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f375,f359,f385])).

fof(f359,plain,
    ( spl10_48
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f375,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl10_48 ),
    inference(resolution,[],[f360,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',cc1_relset_1)).

fof(f360,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f359])).

fof(f361,plain,
    ( spl10_48
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f241,f148,f359])).

fof(f241,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl10_4 ),
    inference(resolution,[],[f99,f149])).

fof(f99,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',dt_u1_orders_2)).

fof(f340,plain,
    ( spl10_42
    | spl10_44
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f204,f176,f338,f332])).

fof(f204,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_12 ),
    inference(resolution,[],[f109,f177])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',t2_subset)).

fof(f280,plain,
    ( ~ spl10_31
    | ~ spl10_33 ),
    inference(avatar_split_clause,[],[f88,f278,f272])).

fof(f278,plain,
    ( spl10_33
  <=> ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f88,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK0),sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f61,f60])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),sK1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),sK1),X0) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t35_orders_2.p',t35_orders_2)).

fof(f178,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f87,f176])).

fof(f87,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f62])).

fof(f150,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f86,f148])).

fof(f86,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f143,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f85,f141])).

fof(f85,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f136,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f84,f134])).

fof(f84,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f62])).
%------------------------------------------------------------------------------
