%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t41_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:06 EDT 2019

% Result     : Theorem 7.33s
% Output     : Refutation 7.33s
% Verified   : 
% Statistics : Number of formulae       :  178 (1385 expanded)
%              Number of leaves         :   37 ( 302 expanded)
%              Depth                    :   12
%              Number of atoms          :  716 (12361 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f250,f332,f380,f452,f1082,f1151,f34515,f34530,f34642,f34745,f50794,f70196])).

fof(f70196,plain,(
    ~ spl7_94 ),
    inference(avatar_contradiction_clause,[],[f70191])).

fof(f70191,plain,
    ( $false
    | ~ spl7_94 ),
    inference(unit_resulting_resolution,[],[f133,f218,f135,f134,f195,f139,f8706,f8711,f8707,f61745,f8705,f175])).

fof(f175,plain,(
    ! [X0,X1] :
      ( ~ v2_yellow_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ v2_waybel_0(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k4_yellow_0(X0),X1) ) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f112])).

fof(f112,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(k4_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => r2_hidden(k4_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t22_waybel_4)).

fof(f8705,plain,(
    m1_subset_1(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f139,f1284,f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',dt_k4_waybel_0)).

fof(f1284,plain,(
    m1_subset_1(k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f195,f139,f518,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k12_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',dt_k12_waybel_0)).

fof(f518,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f288,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',dt_k3_subset_1)).

fof(f288,plain,(
    m1_subset_1(k5_waybel_0(sK0,k4_yellow_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f195,f139,f194,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',dt_k5_waybel_0)).

fof(f194,plain,(
    m1_subset_1(k4_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f139,f177])).

fof(f177,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f116])).

fof(f116,plain,(
    ! [X0] :
      ( m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k4_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',dt_k4_yellow_0)).

fof(f61745,plain,
    ( ~ r2_hidden(k4_yellow_0(sK0),k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))))
    | ~ spl7_94 ),
    inference(unit_resulting_resolution,[],[f325,f34529,f182])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t3_xboole_0)).

fof(f34529,plain,
    ( r1_xboole_0(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_waybel_3(sK0,k4_yellow_0(sK0)))
    | ~ spl7_94 ),
    inference(avatar_component_clause,[],[f34528])).

fof(f34528,plain,
    ( spl7_94
  <=> r1_xboole_0(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_waybel_3(sK0,k4_yellow_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f325,plain,(
    r2_hidden(k4_yellow_0(sK0),k1_waybel_3(sK0,k4_yellow_0(sK0))) ),
    inference(forward_demodulation,[],[f323,f287])).

fof(f287,plain,(
    k1_waybel_3(sK0,k4_yellow_0(sK0)) = a_2_0_waybel_3(sK0,k4_yellow_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f133,f195,f139,f194,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_waybel_3(X0,X1) = a_2_0_waybel_3(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',d3_waybel_3)).

fof(f323,plain,(
    r2_hidden(k4_yellow_0(sK0),a_2_0_waybel_3(sK0,k4_yellow_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f133,f195,f139,f194,f194,f292,f189])).

fof(f189,plain,(
    ! [X2,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r1_waybel_3(X1,X3,X2)
      | r2_hidden(X3,a_2_0_waybel_3(X1,X2)) ) ),
    inference(equality_resolution,[],[f170])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | ~ r1_waybel_3(X1,X3,X2)
      | r2_hidden(X0,a_2_0_waybel_3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f107])).

fof(f107,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_waybel_3(X1,X2))
      <=> ? [X3] :
            ( r1_waybel_3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',fraenkel_a_2_0_waybel_3)).

fof(f292,plain,(
    r1_waybel_3(sK0,k4_yellow_0(sK0),k4_yellow_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f139,f133,f195,f140,f194,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_waybel_3(X0,X1,X1)
      | ~ v1_waybel_3(X1,X0) ) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_3(X1,X0)
          <=> r1_waybel_3(X0,X1,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f109])).

fof(f109,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_3(X1,X0)
          <=> r1_waybel_3(X0,X1,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_waybel_3(X1,X0)
          <=> r1_waybel_3(X0,X1,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',d2_waybel_3)).

fof(f140,plain,(
    v1_waybel_3(k4_yellow_0(sK0),sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ? [X0] :
      ( ( r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
        | ? [X1] :
            ( ! [X2] :
                ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_finset_1(X1)
            & ~ v1_xboole_0(X1) ) )
      & v1_waybel_3(k4_yellow_0(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ? [X0] :
      ( ( r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
        | ? [X1] :
            ( ! [X2] :
                ( ~ r3_orders_2(X0,X2,k4_yellow_0(X0))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_finset_1(X1)
            & ~ v1_xboole_0(X1) ) )
      & v1_waybel_3(k4_yellow_0(X0),X0)
      & l1_orders_2(X0)
      & v3_waybel_3(X0)
      & v2_lattice3(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_waybel_3(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ( v1_waybel_3(k4_yellow_0(X0),X0)
         => ( ~ r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
            & ! [X1] :
                ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                  & v1_finset_1(X1)
                  & ~ v1_xboole_0(X1) )
               => ~ ( ! [X2] :
                        ( m1_subset_1(X2,u1_struct_0(X0))
                       => ~ ( r3_orders_2(X0,X2,k4_yellow_0(X0))
                            & r2_hidden(X2,X1) ) )
                    & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_waybel_3(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ( v1_waybel_3(k4_yellow_0(X0),X0)
       => ( ~ r2_subset_1(k4_waybel_0(X0,k12_waybel_0(X0,k3_subset_1(u1_struct_0(X0),k5_waybel_0(X0,k4_yellow_0(X0))))),k1_waybel_3(X0,k4_yellow_0(X0)))
          & ! [X1] :
              ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v1_finset_1(X1)
                & ~ v1_xboole_0(X1) )
             => ~ ( ! [X2] :
                      ( m1_subset_1(X2,u1_struct_0(X0))
                     => ~ ( r3_orders_2(X0,X2,k4_yellow_0(X0))
                          & r2_hidden(X2,X1) ) )
                  & r1_waybel_3(X0,k2_yellow_0(X0,X1),k4_yellow_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t41_waybel_7)).

fof(f8707,plain,(
    v2_waybel_0(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),sK0) ),
    inference(unit_resulting_resolution,[],[f133,f195,f134,f139,f1283,f1284,f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_0(k4_waybel_0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,X0)
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f59])).

fof(f59,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v2_waybel_0(X1,X0)
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v2_waybel_0(k4_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',fc16_waybel_0)).

fof(f1283,plain,(
    v2_waybel_0(k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0)))),sK0) ),
    inference(unit_resulting_resolution,[],[f134,f139,f133,f137,f135,f518,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_0(k12_waybel_0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k12_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f61])).

fof(f61,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => v2_waybel_0(k12_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',fc22_waybel_0)).

fof(f137,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f8711,plain,(
    v13_waybel_0(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),sK0) ),
    inference(unit_resulting_resolution,[],[f134,f195,f139,f1284,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v13_waybel_0(k4_waybel_0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k4_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v13_waybel_0(k4_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',fc11_waybel_0)).

fof(f8706,plain,(
    ~ v1_xboole_0(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0)))))) ),
    inference(unit_resulting_resolution,[],[f133,f195,f139,f1285,f1284,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(k4_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f63])).

fof(f63,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_waybel_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',fc7_waybel_0)).

fof(f1285,plain,(
    ~ v1_xboole_0(k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))) ),
    inference(unit_resulting_resolution,[],[f135,f218,f139,f195,f518,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(k12_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k12_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f60])).

fof(f60,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k12_waybel_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',fc18_waybel_0)).

fof(f139,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f195,plain,(
    ~ v2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f137,f139,f179])).

fof(f179,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f56])).

fof(f56,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',cc2_lattice3)).

fof(f134,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f135,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f218,plain,(
    v2_yellow_0(sK0) ),
    inference(unit_resulting_resolution,[],[f139,f136,f133,f203,f180])).

fof(f180,plain,(
    ! [X0] :
      ( ~ v24_waybel_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0)
      | v2_yellow_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f120,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_lattice3(X0)
        & v3_orders_2(X0) )
      | ~ v24_waybel_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f119])).

fof(f119,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
        & v1_lattice3(X0)
        & v3_orders_2(X0) )
      | ~ v24_waybel_0(X0)
      | ~ v1_lattice3(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v24_waybel_0(X0)
          & v1_lattice3(X0)
          & v3_orders_2(X0) )
       => ( v2_yellow_0(X0)
          & v1_lattice3(X0)
          & v3_orders_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',cc10_waybel_0)).

fof(f203,plain,(
    v24_waybel_0(sK0) ),
    inference(unit_resulting_resolution,[],[f138,f133,f139,f195,f187])).

fof(f187,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v3_waybel_3(X0)
      | v24_waybel_0(X0) ) ),
    inference(cnf_transformation,[],[f127])).

fof(f127,plain,(
    ! [X0] :
      ( ( v2_waybel_3(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f126])).

fof(f126,plain,(
    ! [X0] :
      ( ( v2_waybel_3(X0)
        & v24_waybel_0(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
      | ~ v3_waybel_3(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f57,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( ( v3_waybel_3(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_waybel_3(X0)
          & v24_waybel_0(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',cc4_waybel_3)).

fof(f138,plain,(
    v3_waybel_3(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f136,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f133,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f50794,plain,
    ( spl7_7
    | ~ spl7_10
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f50792])).

fof(f50792,plain,
    ( $false
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f133,f195,f139,f194,f49925,f50414,f50384,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',redefinition_r3_orders_2)).

fof(f50384,plain,
    ( r1_orders_2(sK0,sK4(sK1),k4_yellow_0(sK0))
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f135,f218,f139,f195,f49925,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,k4_yellow_0(X0)) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f114])).

fof(f114,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,k4_yellow_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,k4_yellow_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t45_yellow_0)).

fof(f50414,plain,
    ( ~ r3_orders_2(sK0,sK4(sK1),k4_yellow_0(sK0))
    | ~ spl7_7
    | ~ spl7_10
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f33902,f49925,f379])).

fof(f379,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | ~ r3_orders_2(sK0,X2,k4_yellow_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl7_14
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X2,k4_yellow_0(sK0))
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f33902,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | ~ spl7_7 ),
    inference(unit_resulting_resolution,[],[f174,f249,f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t2_subset)).

fof(f249,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl7_7
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f174,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',existence_m1_subset_1)).

fof(f49925,plain,
    ( m1_subset_1(sK4(sK1),u1_struct_0(sK0))
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f33902,f331,f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f99])).

fof(f99,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t4_subset)).

fof(f331,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl7_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f34745,plain,(
    ~ spl7_90 ),
    inference(avatar_contradiction_clause,[],[f34675])).

fof(f34675,plain,
    ( $false
    | ~ spl7_90 ),
    inference(unit_resulting_resolution,[],[f325,f34445,f161])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',t7_boole)).

fof(f34445,plain,
    ( v1_xboole_0(k1_waybel_3(sK0,k4_yellow_0(sK0)))
    | ~ spl7_90 ),
    inference(avatar_component_clause,[],[f34444])).

fof(f34444,plain,
    ( spl7_90
  <=> v1_xboole_0(k1_waybel_3(sK0,k4_yellow_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f34642,plain,(
    ~ spl7_88 ),
    inference(avatar_contradiction_clause,[],[f34539])).

fof(f34539,plain,
    ( $false
    | ~ spl7_88 ),
    inference(unit_resulting_resolution,[],[f218,f135,f139,f195,f518,f34439,f152])).

fof(f34439,plain,
    ( v1_xboole_0(k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0)))))
    | ~ spl7_88 ),
    inference(avatar_component_clause,[],[f34438])).

fof(f34438,plain,
    ( spl7_88
  <=> v1_xboole_0(k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f34530,plain,
    ( spl7_88
    | spl7_94
    | spl7_90
    | ~ spl7_93
    | ~ spl7_4
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f7356,f1149,f242,f34450,f34444,f34528,f34438])).

fof(f34450,plain,
    ( spl7_93
  <=> ~ m1_subset_1(k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).

fof(f242,plain,
    ( spl7_4
  <=> r2_subset_1(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_waybel_3(sK0,k4_yellow_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1149,plain,
    ( spl7_30
  <=> ! [X1] :
        ( v1_xboole_0(X1)
        | ~ v1_xboole_0(k4_waybel_0(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f7356,plain,
    ( ~ m1_subset_1(k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k1_waybel_3(sK0,k4_yellow_0(sK0)))
    | r1_xboole_0(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_waybel_3(sK0,k4_yellow_0(sK0)))
    | v1_xboole_0(k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0)))))
    | ~ spl7_4
    | ~ spl7_30 ),
    inference(resolution,[],[f1175,f243])).

fof(f243,plain,
    ( r2_subset_1(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_waybel_3(sK0,k4_yellow_0(sK0)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f242])).

fof(f1175,plain,
    ( ! [X8,X9] :
        ( ~ r2_subset_1(k4_waybel_0(sK0,X8),X9)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X9)
        | r1_xboole_0(k4_waybel_0(sK0,X8),X9)
        | v1_xboole_0(X8) )
    | ~ spl7_30 ),
    inference(resolution,[],[f1150,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | r1_xboole_0(X0,X1)
      | ~ r2_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r2_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t41_waybel_7.p',redefinition_r2_subset_1)).

fof(f1150,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(k4_waybel_0(sK0,X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f1149])).

fof(f34515,plain,(
    spl7_93 ),
    inference(avatar_contradiction_clause,[],[f34507])).

fof(f34507,plain,
    ( $false
    | ~ spl7_93 ),
    inference(unit_resulting_resolution,[],[f195,f139,f518,f34451,f151])).

fof(f34451,plain,
    ( ~ m1_subset_1(k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_93 ),
    inference(avatar_component_clause,[],[f34450])).

fof(f1151,plain,
    ( spl7_30
    | ~ spl7_3
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f206,f428,f235,f1149])).

fof(f235,plain,
    ( spl7_3
  <=> ~ l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f428,plain,
    ( spl7_19
  <=> ~ v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f206,plain,(
    ! [X1] :
      ( ~ v3_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(k4_waybel_0(sK0,X1)) ) ),
    inference(resolution,[],[f195,f148])).

fof(f1082,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f1079])).

fof(f1079,plain,
    ( $false
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f139,f236])).

fof(f236,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f235])).

fof(f452,plain,(
    spl7_19 ),
    inference(avatar_contradiction_clause,[],[f449])).

fof(f449,plain,
    ( $false
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f133,f429])).

fof(f429,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f428])).

fof(f380,plain,
    ( spl7_4
    | spl7_14 ),
    inference(avatar_split_clause,[],[f128,f378,f242])).

fof(f128,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | ~ r3_orders_2(sK0,X2,k4_yellow_0(sK0))
      | r2_subset_1(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_waybel_3(sK0,k4_yellow_0(sK0))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f332,plain,
    ( spl7_4
    | spl7_10 ),
    inference(avatar_split_clause,[],[f131,f330,f242])).

fof(f131,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_subset_1(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_waybel_3(sK0,k4_yellow_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).

fof(f250,plain,
    ( spl7_4
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f129,f248,f242])).

fof(f129,plain,
    ( ~ v1_xboole_0(sK1)
    | r2_subset_1(k4_waybel_0(sK0,k12_waybel_0(sK0,k3_subset_1(u1_struct_0(sK0),k5_waybel_0(sK0,k4_yellow_0(sK0))))),k1_waybel_3(sK0,k4_yellow_0(sK0))) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
