%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t19_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:04 EDT 2019

% Result     : Theorem 3.06s
% Output     : Refutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  238 (1043 expanded)
%              Number of leaves         :   42 ( 280 expanded)
%              Depth                    :   26
%              Number of atoms          : 1134 (10764 expanded)
%              Number of equality atoms :  108 ( 884 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4799,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f184,f399,f413,f421,f423,f425,f429,f499,f824,f827,f833,f835,f1229,f1231,f1406,f1444,f1488,f1496,f1502,f1508,f1523,f1528,f1533,f4754,f4774,f4791])).

fof(f4791,plain,
    ( spl11_2
    | ~ spl11_139
    | ~ spl11_5
    | ~ spl11_7
    | spl11_256
    | ~ spl11_57
    | ~ spl11_141
    | ~ spl11_143
    | ~ spl11_145
    | ~ spl11_229
    | ~ spl11_842 ),
    inference(avatar_split_clause,[],[f4790,f4752,f1227,f820,f817,f814,f416,f1494,f182,f179,f811,f4772])).

fof(f4772,plain,
    ( spl11_2
  <=> v2_waybel_7(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f811,plain,
    ( spl11_139
  <=> ~ v3_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_139])])).

fof(f179,plain,
    ( spl11_5
  <=> ~ v13_waybel_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f182,plain,
    ( spl11_7
  <=> ~ v2_waybel_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f1494,plain,
    ( spl11_256
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_256])])).

fof(f416,plain,
    ( spl11_57
  <=> ~ l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_57])])).

fof(f814,plain,
    ( spl11_141
  <=> ~ v1_lattice3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_141])])).

fof(f817,plain,
    ( spl11_143
  <=> ~ v5_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_143])])).

fof(f820,plain,
    ( spl11_145
  <=> ~ v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_145])])).

fof(f1227,plain,
    ( spl11_229
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_229])])).

fof(f4752,plain,
    ( spl11_842
  <=> r2_hidden(sK4(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_842])])).

fof(f4790,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v2_waybel_0(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v3_orders_2(sK1)
    | v2_waybel_7(sK2,sK1)
    | ~ spl11_842 ),
    inference(forward_demodulation,[],[f4782,f379])).

fof(f379,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f375])).

fof(f375,plain,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(superposition,[],[f372,f109])).

fof(f109,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v2_waybel_7(X2,X1)
                | ~ v13_waybel_0(X2,X1)
                | ~ v2_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X2,X0)
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v1_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v2_waybel_7(X2,X1)
                | ~ v13_waybel_0(X2,X1)
                | ~ v2_waybel_0(X2,X1)
                | v1_xboole_0(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_waybel_7(X2,X0)
              & v13_waybel_0(X2,X0)
              & v2_waybel_0(X2,X0)
              & ~ v1_xboole_0(X2) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1)
          & v2_lattice3(X1)
          & v1_lattice3(X1)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & v2_lattice3(X1)
              & v1_lattice3(X1)
              & v5_orders_2(X1)
              & v4_orders_2(X1)
              & v3_orders_2(X1) )
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & v2_waybel_7(X2,X0)
                    & v13_waybel_0(X2,X0)
                    & v2_waybel_0(X2,X0)
                    & ~ v1_xboole_0(X2) )
                 => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                    & v2_waybel_7(X2,X1)
                    & v13_waybel_0(X2,X1)
                    & v2_waybel_0(X2,X1)
                    & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & v2_lattice3(X1)
            & v1_lattice3(X1)
            & v5_orders_2(X1)
            & v4_orders_2(X1)
            & v3_orders_2(X1) )
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v2_waybel_7(X2,X0)
                  & v13_waybel_0(X2,X0)
                  & v2_waybel_0(X2,X0)
                  & ~ v1_xboole_0(X2) )
               => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_7(X2,X1)
                  & v13_waybel_0(X2,X1)
                  & v2_waybel_0(X2,X1)
                  & ~ v1_xboole_0(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t19_waybel_7.p',t19_waybel_7)).

fof(f372,plain,(
    ! [X6,X7] :
      ( g1_orders_2(X6,X7) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK0) = X6 ) ),
    inference(resolution,[],[f360,f115])).

fof(f115,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f360,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | u1_struct_0(X0) = X1
      | g1_orders_2(X1,X2) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ) ),
    inference(resolution,[],[f151,f118])).

fof(f118,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t19_waybel_7.p',dt_u1_orders_2)).

fof(f151,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t19_waybel_7.p',free_g1_orders_2)).

fof(f4782,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v2_waybel_0(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_orders_2(sK1)
    | v2_waybel_7(sK2,sK1)
    | ~ spl11_842 ),
    inference(resolution,[],[f4753,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v2_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v2_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k13_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t19_waybel_7.p',d2_waybel_7)).

fof(f4753,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | ~ spl11_842 ),
    inference(avatar_component_clause,[],[f4752])).

fof(f4774,plain,
    ( spl11_2
    | ~ spl11_139
    | ~ spl11_5
    | ~ spl11_7
    | spl11_256
    | ~ spl11_57
    | ~ spl11_141
    | ~ spl11_143
    | ~ spl11_145
    | ~ spl11_229
    | ~ spl11_840 ),
    inference(avatar_split_clause,[],[f4770,f4749,f1227,f820,f817,f814,f416,f1494,f182,f179,f811,f4772])).

fof(f4749,plain,
    ( spl11_840
  <=> r2_hidden(sK5(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_840])])).

fof(f4770,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v2_waybel_0(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v3_orders_2(sK1)
    | v2_waybel_7(sK2,sK1)
    | ~ spl11_840 ),
    inference(forward_demodulation,[],[f4762,f379])).

fof(f4762,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v2_waybel_0(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_orders_2(sK1)
    | v2_waybel_7(sK2,sK1)
    | ~ spl11_840 ),
    inference(resolution,[],[f4750,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v2_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f4750,plain,
    ( r2_hidden(sK5(sK1,sK2),sK2)
    | ~ spl11_840 ),
    inference(avatar_component_clause,[],[f4749])).

fof(f4754,plain,
    ( spl11_840
    | spl11_842
    | ~ spl11_259
    | ~ spl11_261
    | ~ spl11_248
    | ~ spl11_252
    | ~ spl11_254
    | ~ spl11_258
    | ~ spl11_260 ),
    inference(avatar_split_clause,[],[f4740,f1506,f1500,f1491,f1442,f1404,f3054,f2997,f4752,f4749])).

fof(f2997,plain,
    ( spl11_259
  <=> ~ m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_259])])).

fof(f3054,plain,
    ( spl11_261
  <=> ~ m1_subset_1(sK5(sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_261])])).

fof(f1404,plain,
    ( spl11_248
  <=> ! [X5,X4] :
        ( k13_lattice3(sK1,X4,X5) = k1_yellow_0(sK1,k2_tarski(X4,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_248])])).

fof(f1442,plain,
    ( spl11_252
  <=> ! [X5,X4] :
        ( k13_lattice3(sK0,X4,X5) = k1_yellow_0(sK0,k2_tarski(X4,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_252])])).

fof(f1491,plain,
    ( spl11_254
  <=> r2_hidden(k13_lattice3(sK1,sK4(sK1,sK2),sK5(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_254])])).

fof(f1500,plain,
    ( spl11_258
  <=> m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_258])])).

fof(f1506,plain,
    ( spl11_260
  <=> m1_subset_1(sK5(sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_260])])).

fof(f4740,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK0))
    | r2_hidden(sK4(sK1,sK2),sK2)
    | r2_hidden(sK5(sK1,sK2),sK2)
    | ~ spl11_248
    | ~ spl11_252
    | ~ spl11_254
    | ~ spl11_258
    | ~ spl11_260 ),
    inference(resolution,[],[f4680,f1743])).

fof(f1743,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k13_lattice3(sK0,X0,X1),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,sK2)
      | r2_hidden(X1,sK2) ) ),
    inference(global_subsumption,[],[f98,f99,f101,f102,f1739])).

fof(f1739,plain,(
    ! [X0,X1] :
      ( ~ v2_waybel_0(sK2,sK0)
      | v1_xboole_0(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(k13_lattice3(sK0,X0,X1),sK2)
      | r2_hidden(X0,sK2)
      | r2_hidden(X1,sK2)
      | ~ v2_waybel_7(sK2,sK0) ) ),
    inference(resolution,[],[f1515,f100])).

fof(f100,plain,(
    v13_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f1515,plain,(
    ! [X4,X5,X3] :
      ( ~ v13_waybel_0(X3,sK0)
      | ~ v2_waybel_0(X3,sK0)
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(k13_lattice3(sK0,X4,X5),X3)
      | r2_hidden(X4,X3)
      | r2_hidden(X5,X3)
      | ~ v2_waybel_7(X3,sK0) ) ),
    inference(global_subsumption,[],[f110,f111,f113,f115,f1510])).

fof(f1510,plain,(
    ! [X4,X5,X3] :
      ( ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v1_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(X3)
      | ~ v2_waybel_0(X3,sK0)
      | ~ v13_waybel_0(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(k13_lattice3(sK0,X4,X5),X3)
      | r2_hidden(X4,X3)
      | r2_hidden(X5,X3)
      | ~ v2_waybel_7(X3,sK0) ) ),
    inference(resolution,[],[f137,f112])).

fof(f112,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(k13_lattice3(X0,X2,X3),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v2_waybel_7(X1,X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f113,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f111,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f110,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f102,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f101,plain,(
    v2_waybel_7(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,(
    v2_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f98,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f4680,plain,
    ( r2_hidden(k13_lattice3(sK0,sK4(sK1,sK2),sK5(sK1,sK2)),sK2)
    | ~ spl11_248
    | ~ spl11_252
    | ~ spl11_254
    | ~ spl11_258
    | ~ spl11_260 ),
    inference(backward_demodulation,[],[f3634,f1492])).

fof(f1492,plain,
    ( r2_hidden(k13_lattice3(sK1,sK4(sK1,sK2),sK5(sK1,sK2)),sK2)
    | ~ spl11_254 ),
    inference(avatar_component_clause,[],[f1491])).

fof(f3634,plain,
    ( k13_lattice3(sK0,sK4(sK1,sK2),sK5(sK1,sK2)) = k13_lattice3(sK1,sK4(sK1,sK2),sK5(sK1,sK2))
    | ~ spl11_248
    | ~ spl11_252
    | ~ spl11_258
    | ~ spl11_260 ),
    inference(resolution,[],[f2770,f1507])).

fof(f1507,plain,
    ( m1_subset_1(sK5(sK1,sK2),u1_struct_0(sK0))
    | ~ spl11_260 ),
    inference(avatar_component_clause,[],[f1506])).

fof(f2770,plain,
    ( ! [X23] :
        ( ~ m1_subset_1(X23,u1_struct_0(sK0))
        | k13_lattice3(sK0,sK4(sK1,sK2),X23) = k13_lattice3(sK1,sK4(sK1,sK2),X23) )
    | ~ spl11_248
    | ~ spl11_252
    | ~ spl11_258 ),
    inference(resolution,[],[f2754,f1501])).

fof(f1501,plain,
    ( m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK0))
    | ~ spl11_258 ),
    inference(avatar_component_clause,[],[f1500])).

fof(f2754,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k13_lattice3(sK0,X4,X5) = k13_lattice3(sK1,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl11_248
    | ~ spl11_252 ),
    inference(duplicate_literal_removal,[],[f2752])).

fof(f2752,plain,
    ( ! [X4,X5] :
        ( k13_lattice3(sK0,X4,X5) = k13_lattice3(sK1,X4,X5)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl11_248
    | ~ spl11_252 ),
    inference(superposition,[],[f1443,f2725])).

fof(f2725,plain,
    ( ! [X2,X3] :
        ( k13_lattice3(sK1,X2,X3) = k1_yellow_0(sK0,k2_tarski(X2,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl11_248 ),
    inference(duplicate_literal_removal,[],[f2721])).

fof(f2721,plain,
    ( ! [X2,X3] :
        ( k13_lattice3(sK1,X2,X3) = k1_yellow_0(sK0,k2_tarski(X2,X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl11_248 ),
    inference(superposition,[],[f1405,f2576])).

fof(f2576,plain,(
    ! [X6,X7] :
      ( k1_yellow_0(sK0,k2_tarski(X6,X7)) = k1_yellow_0(sK1,k2_tarski(X6,X7))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    inference(trivial_inequality_removal,[],[f2573])).

fof(f2573,plain,(
    ! [X6,X7] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | k1_yellow_0(sK0,k2_tarski(X6,X7)) = k1_yellow_0(sK1,k2_tarski(X6,X7))
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f1033,f115])).

fof(f1033,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | k1_yellow_0(sK1,k2_tarski(X1,X2)) = k1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f108,f1032])).

fof(f1032,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(sK1)
      | k1_yellow_0(sK1,k2_tarski(X1,X2)) = k1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f1031,f380])).

fof(f380,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) ),
    inference(backward_demodulation,[],[f379,f109])).

fof(f1031,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(sK1)
      | k1_yellow_0(sK1,k2_tarski(X1,X2)) = k1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f1029,f379])).

fof(f1029,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ l1_orders_2(sK1)
      | k1_yellow_0(sK1,k2_tarski(X1,X2)) = k1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f121,f883])).

fof(f883,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(sK1,k2_tarski(X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f106,f108,f882])).

fof(f882,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK1)
      | r1_yellow_0(sK1,k2_tarski(X0,X1))
      | ~ v1_lattice3(sK1) ) ),
    inference(forward_demodulation,[],[f881,f379])).

fof(f881,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | r1_yellow_0(sK1,k2_tarski(X0,X1))
      | ~ v1_lattice3(sK1) ) ),
    inference(forward_demodulation,[],[f879,f379])).

fof(f879,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | r1_yellow_0(sK1,k2_tarski(X0,X1))
      | ~ v1_lattice3(sK1) ) ),
    inference(resolution,[],[f141,f105])).

fof(f105,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v1_lattice3(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( v1_lattice3(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( r1_yellow_0(X0,k2_tarski(X1,X2))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ( v1_lattice3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => r1_yellow_0(X0,k2_tarski(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t19_waybel_7.p',t20_yellow_0)).

fof(f106,plain,(
    v1_lattice3(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X2)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
              | ~ r1_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2)
              | ~ r1_yellow_0(X0,X2) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( r1_yellow_0(X0,X2)
               => k1_yellow_0(X0,X2) = k1_yellow_0(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t19_waybel_7.p',t26_yellow_0)).

fof(f108,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f1405,plain,
    ( ! [X4,X5] :
        ( k13_lattice3(sK1,X4,X5) = k1_yellow_0(sK1,k2_tarski(X4,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl11_248 ),
    inference(avatar_component_clause,[],[f1404])).

fof(f1443,plain,
    ( ! [X4,X5] :
        ( k13_lattice3(sK0,X4,X5) = k1_yellow_0(sK0,k2_tarski(X4,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl11_252 ),
    inference(avatar_component_clause,[],[f1442])).

fof(f1533,plain,
    ( ~ spl11_229
    | ~ spl11_63
    | ~ spl11_240 ),
    inference(avatar_split_clause,[],[f1532,f1308,f464,f1227])).

fof(f464,plain,
    ( spl11_63
  <=> ~ l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_63])])).

fof(f1308,plain,
    ( spl11_240
  <=> ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ v2_waybel_0(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_240])])).

fof(f1532,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_240 ),
    inference(trivial_inequality_removal,[],[f1529])).

fof(f1529,plain,
    ( ~ l1_orders_2(sK0)
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_240 ),
    inference(resolution,[],[f1309,f99])).

fof(f1309,plain,
    ( ! [X0] :
        ( ~ v2_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl11_240 ),
    inference(avatar_component_clause,[],[f1308])).

fof(f1528,plain,
    ( ~ spl11_57
    | spl11_240
    | ~ spl11_229
    | spl11_7 ),
    inference(avatar_split_clause,[],[f1527,f182,f1227,f1308,f416])).

fof(f1527,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_7 ),
    inference(forward_demodulation,[],[f1526,f379])).

fof(f1526,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_7 ),
    inference(forward_demodulation,[],[f1525,f379])).

fof(f1525,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_7 ),
    inference(forward_demodulation,[],[f1524,f1037])).

fof(f1037,plain,(
    u1_orders_2(sK0) = u1_orders_2(sK1) ),
    inference(equality_resolution,[],[f1027])).

fof(f1027,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_orders_2(sK1) = X1 ) ),
    inference(superposition,[],[f595,f380])).

fof(f595,plain,(
    ! [X0,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK1))
      | u1_orders_2(sK1) = X1 ) ),
    inference(resolution,[],[f389,f152])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f77])).

fof(f389,plain,(
    m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(global_subsumption,[],[f108,f382])).

fof(f382,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK1) ),
    inference(superposition,[],[f118,f379])).

fof(f1524,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK1)
        | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_7 ),
    inference(resolution,[],[f183,f170])).

fof(f170,plain,(
    ! [X0,X3,X1] :
      ( v2_waybel_0(X3,X1)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_waybel_0(X3,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f124])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X2 != X3
      | ~ v2_waybel_0(X2,X0)
      | v2_waybel_0(X3,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_waybel_0(X3,X1)
                  | ~ v2_waybel_0(X2,X0)
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_waybel_0(X3,X1)
                  | ~ v2_waybel_0(X2,X0)
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_waybel_0(X2,X0)
                        & X2 = X3 )
                     => v2_waybel_0(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t19_waybel_7.p',t4_waybel_0)).

fof(f183,plain,
    ( ~ v2_waybel_0(sK2,sK1)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f182])).

fof(f1523,plain,(
    ~ spl11_256 ),
    inference(avatar_contradiction_clause,[],[f1516])).

fof(f1516,plain,
    ( $false
    | ~ spl11_256 ),
    inference(resolution,[],[f1495,f98])).

fof(f1495,plain,
    ( v1_xboole_0(sK2)
    | ~ spl11_256 ),
    inference(avatar_component_clause,[],[f1494])).

fof(f1508,plain,
    ( ~ spl11_139
    | ~ spl11_5
    | ~ spl11_7
    | spl11_256
    | ~ spl11_57
    | ~ spl11_141
    | ~ spl11_143
    | ~ spl11_145
    | ~ spl11_229
    | spl11_260
    | spl11_3 ),
    inference(avatar_split_clause,[],[f1504,f176,f1506,f1227,f820,f817,f814,f416,f1494,f182,f179,f811])).

fof(f176,plain,
    ( spl11_3
  <=> ~ v2_waybel_7(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f1504,plain,
    ( m1_subset_1(sK5(sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v2_waybel_0(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(forward_demodulation,[],[f1503,f379])).

fof(f1503,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v2_waybel_0(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | m1_subset_1(sK5(sK1,sK2),u1_struct_0(sK1))
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(forward_demodulation,[],[f1353,f379])).

fof(f1353,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v2_waybel_0(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK5(sK1,sK2),u1_struct_0(sK1))
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(resolution,[],[f133,f177])).

fof(f177,plain,
    ( ~ v2_waybel_7(sK2,sK1)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f176])).

fof(f133,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1502,plain,
    ( ~ spl11_139
    | ~ spl11_5
    | ~ spl11_7
    | spl11_256
    | ~ spl11_57
    | ~ spl11_141
    | ~ spl11_143
    | ~ spl11_145
    | ~ spl11_229
    | spl11_258
    | spl11_3 ),
    inference(avatar_split_clause,[],[f1498,f176,f1500,f1227,f820,f817,f814,f416,f1494,f182,f179,f811])).

fof(f1498,plain,
    ( m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v2_waybel_0(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(forward_demodulation,[],[f1497,f379])).

fof(f1497,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v2_waybel_0(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK1))
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(forward_demodulation,[],[f1369,f379])).

fof(f1369,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v2_waybel_0(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK4(sK1,sK2),u1_struct_0(sK1))
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(resolution,[],[f138,f177])).

fof(f138,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1496,plain,
    ( ~ spl11_139
    | spl11_254
    | ~ spl11_5
    | ~ spl11_7
    | spl11_256
    | ~ spl11_57
    | ~ spl11_141
    | ~ spl11_143
    | ~ spl11_145
    | ~ spl11_229
    | spl11_3 ),
    inference(avatar_split_clause,[],[f1489,f176,f1227,f820,f817,f814,f416,f1494,f182,f179,f1491,f811])).

fof(f1489,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v2_waybel_0(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | r2_hidden(k13_lattice3(sK1,sK4(sK1,sK2),sK5(sK1,sK2)),sK2)
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(forward_demodulation,[],[f1428,f379])).

fof(f1428,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v1_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | v1_xboole_0(sK2)
    | ~ v2_waybel_0(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(k13_lattice3(sK1,sK4(sK1,sK2),sK5(sK1,sK2)),sK2)
    | ~ v3_orders_2(sK1)
    | ~ spl11_3 ),
    inference(resolution,[],[f134,f177])).

fof(f134,plain,(
    ! [X0,X1] :
      ( v2_waybel_7(X1,X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k13_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f1488,plain,
    ( ~ spl11_229
    | ~ spl11_63
    | ~ spl11_226 ),
    inference(avatar_split_clause,[],[f1487,f1224,f464,f1227])).

fof(f1224,plain,
    ( spl11_226
  <=> ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(X0)
        | ~ v13_waybel_0(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_226])])).

fof(f1487,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_226 ),
    inference(trivial_inequality_removal,[],[f1484])).

fof(f1484,plain,
    ( ~ l1_orders_2(sK0)
    | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_226 ),
    inference(resolution,[],[f1225,f100])).

fof(f1225,plain,
    ( ! [X0] :
        ( ~ v13_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0)
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl11_226 ),
    inference(avatar_component_clause,[],[f1224])).

fof(f1444,plain,
    ( spl11_50
    | spl11_252 ),
    inference(avatar_split_clause,[],[f1433,f1442,f1396])).

fof(f1396,plain,
    ( spl11_50
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f1433,plain,(
    ! [X4,X5] :
      ( k13_lattice3(sK0,X4,X5) = k1_yellow_0(sK0,k2_tarski(X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f1431])).

fof(f1431,plain,(
    ! [X4,X5] :
      ( k13_lattice3(sK0,X4,X5) = k1_yellow_0(sK0,k2_tarski(X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f1090,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k2_tarski(X1,X2) = k7_domain_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t19_waybel_7.p',redefinition_k7_domain_1)).

fof(f1090,plain,(
    ! [X2,X3] :
      ( k13_lattice3(sK0,X2,X3) = k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f110,f111,f113,f115,f1085])).

fof(f1085,plain,(
    ! [X2,X3] :
      ( ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ v1_lattice3(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k13_lattice3(sK0,X2,X3) = k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X2,X3)) ) ),
    inference(resolution,[],[f132,f112])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t19_waybel_7.p',t41_yellow_0)).

fof(f1406,plain,
    ( spl11_50
    | spl11_248 ),
    inference(avatar_split_clause,[],[f1392,f1404,f1396])).

fof(f1392,plain,(
    ! [X4,X5] :
      ( k13_lattice3(sK1,X4,X5) = k1_yellow_0(sK1,k2_tarski(X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f1388])).

fof(f1388,plain,(
    ! [X4,X5] :
      ( k13_lattice3(sK1,X4,X5) = k1_yellow_0(sK1,k2_tarski(X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f1089,f158])).

fof(f1089,plain,(
    ! [X0,X1] :
      ( k13_lattice3(sK1,X0,X1) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f103,f104,f106,f108,f1088])).

fof(f1088,plain,(
    ! [X0,X1] :
      ( k13_lattice3(sK1,X0,X1) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK0),X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | ~ v1_lattice3(sK1)
      | ~ l1_orders_2(sK1) ) ),
    inference(forward_demodulation,[],[f1087,f379])).

fof(f1087,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | ~ v1_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | k13_lattice3(sK1,X0,X1) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) ) ),
    inference(forward_demodulation,[],[f1086,f379])).

fof(f1086,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | ~ v1_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k13_lattice3(sK1,X0,X1) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) ) ),
    inference(forward_demodulation,[],[f1084,f379])).

fof(f1084,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | ~ v1_lattice3(sK1)
      | ~ l1_orders_2(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | k13_lattice3(sK1,X0,X1) = k1_yellow_0(sK1,k7_domain_1(u1_struct_0(sK1),X0,X1)) ) ),
    inference(resolution,[],[f132,f105])).

fof(f104,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f1231,plain,(
    spl11_229 ),
    inference(avatar_contradiction_clause,[],[f1230])).

fof(f1230,plain,
    ( $false
    | ~ spl11_229 ),
    inference(resolution,[],[f1228,f102])).

fof(f1228,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_229 ),
    inference(avatar_component_clause,[],[f1227])).

fof(f1229,plain,
    ( ~ spl11_57
    | spl11_226
    | ~ spl11_229
    | spl11_5 ),
    inference(avatar_split_clause,[],[f1222,f179,f1227,f1224,f416])).

fof(f1222,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v13_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f1221,f379])).

fof(f1221,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v13_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f1220,f379])).

fof(f1220,plain,
    ( ! [X0] :
        ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ l1_orders_2(sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v13_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f1219,f1037])).

fof(f1219,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK1)
        | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v13_waybel_0(sK2,X0)
        | ~ l1_orders_2(X0) )
    | ~ spl11_5 ),
    inference(resolution,[],[f169,f180])).

fof(f180,plain,
    ( ~ v13_waybel_0(sK2,sK1)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f179])).

fof(f169,plain,(
    ! [X0,X3,X1] :
      ( v13_waybel_0(X3,X1)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v13_waybel_0(X3,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f122])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ l1_orders_2(X1)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X2 != X3
      | ~ v13_waybel_0(X2,X0)
      | v13_waybel_0(X3,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v13_waybel_0(X3,X1)
                      | ~ v13_waybel_0(X2,X0) )
                    & ( v12_waybel_0(X3,X1)
                      | ~ v12_waybel_0(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v13_waybel_0(X3,X1)
                      | ~ v13_waybel_0(X2,X0) )
                    & ( v12_waybel_0(X3,X1)
                      | ~ v12_waybel_0(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( ( v13_waybel_0(X2,X0)
                         => v13_waybel_0(X3,X1) )
                        & ( v12_waybel_0(X2,X0)
                         => v12_waybel_0(X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t19_waybel_7.p',t25_waybel_0)).

fof(f835,plain,(
    spl11_145 ),
    inference(avatar_contradiction_clause,[],[f834])).

fof(f834,plain,
    ( $false
    | ~ spl11_145 ),
    inference(resolution,[],[f821,f104])).

fof(f821,plain,
    ( ~ v4_orders_2(sK1)
    | ~ spl11_145 ),
    inference(avatar_component_clause,[],[f820])).

fof(f833,plain,(
    spl11_143 ),
    inference(avatar_contradiction_clause,[],[f832])).

fof(f832,plain,
    ( $false
    | ~ spl11_143 ),
    inference(resolution,[],[f818,f105])).

fof(f818,plain,
    ( ~ v5_orders_2(sK1)
    | ~ spl11_143 ),
    inference(avatar_component_clause,[],[f817])).

fof(f827,plain,(
    spl11_141 ),
    inference(avatar_contradiction_clause,[],[f825])).

fof(f825,plain,
    ( $false
    | ~ spl11_141 ),
    inference(resolution,[],[f815,f106])).

fof(f815,plain,
    ( ~ v1_lattice3(sK1)
    | ~ spl11_141 ),
    inference(avatar_component_clause,[],[f814])).

fof(f824,plain,(
    spl11_139 ),
    inference(avatar_contradiction_clause,[],[f823])).

fof(f823,plain,
    ( $false
    | ~ spl11_139 ),
    inference(resolution,[],[f812,f103])).

fof(f812,plain,
    ( ~ v3_orders_2(sK1)
    | ~ spl11_139 ),
    inference(avatar_component_clause,[],[f811])).

fof(f499,plain,(
    spl11_63 ),
    inference(avatar_contradiction_clause,[],[f498])).

fof(f498,plain,
    ( $false
    | ~ spl11_63 ),
    inference(resolution,[],[f465,f115])).

fof(f465,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_63 ),
    inference(avatar_component_clause,[],[f464])).

fof(f429,plain,(
    spl11_1 ),
    inference(avatar_contradiction_clause,[],[f428])).

fof(f428,plain,
    ( $false
    | ~ spl11_1 ),
    inference(resolution,[],[f381,f102])).

fof(f381,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_1 ),
    inference(backward_demodulation,[],[f379,f174])).

fof(f174,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl11_1
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f425,plain,(
    spl11_59 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | ~ spl11_59 ),
    inference(resolution,[],[f420,f107])).

fof(f107,plain,(
    v2_lattice3(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f420,plain,
    ( ~ v2_lattice3(sK1)
    | ~ spl11_59 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl11_59
  <=> ~ v2_lattice3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_59])])).

fof(f423,plain,(
    spl11_57 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | ~ spl11_57 ),
    inference(resolution,[],[f417,f108])).

fof(f417,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl11_57 ),
    inference(avatar_component_clause,[],[f416])).

fof(f421,plain,
    ( ~ spl11_57
    | ~ spl11_59
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f414,f391,f419,f416])).

fof(f391,plain,
    ( spl11_46
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f414,plain,
    ( ~ v2_lattice3(sK1)
    | ~ l1_orders_2(sK1)
    | ~ spl11_46 ),
    inference(resolution,[],[f392,f120])).

fof(f120,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t19_waybel_7.p',cc2_lattice3)).

fof(f392,plain,
    ( v2_struct_0(sK1)
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f391])).

fof(f413,plain,(
    spl11_49 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | ~ spl11_49 ),
    inference(resolution,[],[f411,f108])).

fof(f411,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl11_49 ),
    inference(resolution,[],[f395,f117])).

fof(f117,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t19_waybel_7.p',dt_l1_orders_2)).

fof(f395,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl11_49 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl11_49
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).

fof(f399,plain,
    ( spl11_46
    | ~ spl11_49
    | ~ spl11_51 ),
    inference(avatar_split_clause,[],[f383,f397,f394,f391])).

fof(f397,plain,
    ( spl11_51
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).

fof(f383,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f126,f379])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
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
    file('/export/starexec/sandbox/benchmark/waybel_7__t19_waybel_7.p',fc2_struct_0)).

fof(f184,plain,
    ( ~ spl11_1
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f171,f182,f179,f176,f173])).

fof(f171,plain,
    ( ~ v2_waybel_0(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_7(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_subsumption,[],[f98,f97])).

fof(f97,plain,
    ( v1_xboole_0(sK2)
    | ~ v2_waybel_0(sK2,sK1)
    | ~ v13_waybel_0(sK2,sK1)
    | ~ v2_waybel_7(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
