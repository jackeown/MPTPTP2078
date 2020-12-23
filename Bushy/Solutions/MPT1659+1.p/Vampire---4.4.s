%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t39_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:49 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  304 ( 850 expanded)
%              Number of leaves         :   83 ( 366 expanded)
%              Depth                    :   10
%              Number of atoms          :  934 (2585 expanded)
%              Number of equality atoms :   59 ( 192 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f864,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f138,f145,f152,f159,f166,f173,f180,f187,f194,f201,f208,f215,f222,f232,f239,f246,f257,f268,f275,f300,f314,f328,f353,f361,f369,f379,f395,f442,f449,f462,f477,f487,f517,f527,f548,f563,f635,f656,f684,f691,f722,f730,f737,f766,f800,f811,f812,f819,f826,f835,f843,f850,f857])).

fof(f857,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_26
    | spl6_37
    | ~ spl6_56
    | spl6_63
    | ~ spl6_80
    | ~ spl6_94 ),
    inference(avatar_contradiction_clause,[],[f856])).

fof(f856,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_37
    | ~ spl6_56
    | ~ spl6_63
    | ~ spl6_80
    | ~ spl6_94 ),
    inference(subsumption_resolution,[],[f855,f461])).

fof(f461,plain,
    ( k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) != sK1
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f460])).

fof(f460,plain,
    ( spl6_63
  <=> k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f855,plain,
    ( k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) = sK1
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_37
    | ~ spl6_56
    | ~ spl6_80
    | ~ spl6_94 ),
    inference(forward_demodulation,[],[f854,f799])).

fof(f799,plain,
    ( k2_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl6_94 ),
    inference(avatar_component_clause,[],[f798])).

fof(f798,plain,
    ( spl6_94
  <=> k2_yellow_0(sK0,k1_tarski(sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f854,plain,
    ( k2_yellow_0(sK0,k1_tarski(sK1)) = k2_yellow_0(sK0,k6_waybel_0(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_37
    | ~ spl6_56
    | ~ spl6_80 ),
    inference(forward_demodulation,[],[f851,f708])).

fof(f708,plain,
    ( k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f701,f383])).

fof(f383,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl6_26
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f267,f221,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',redefinition_k6_domain_1)).

fof(f221,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl6_26
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f267,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl6_37
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f701,plain,
    ( k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f130,f158,f221,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',d18_waybel_0)).

fof(f158,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl6_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f130,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f851,plain,
    ( k2_yellow_0(sK0,k1_tarski(sK1)) = k2_yellow_0(sK0,k4_waybel_0(sK0,k1_tarski(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_56
    | ~ spl6_80 ),
    inference(unit_resulting_resolution,[],[f130,f137,f144,f158,f655,f441,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1))
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1))
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_yellow_0(X0,X1)
           => k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',t38_waybel_0)).

fof(f441,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl6_56
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f655,plain,
    ( r2_yellow_0(sK0,k1_tarski(sK1))
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f654])).

fof(f654,plain,
    ( spl6_80
  <=> r2_yellow_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f144,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f137,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl6_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f850,plain,
    ( ~ spl6_105
    | spl6_83 ),
    inference(avatar_split_clause,[],[f693,f682,f848])).

fof(f848,plain,
    ( spl6_105
  <=> ~ r2_hidden(sK1,sK2(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).

fof(f682,plain,
    ( spl6_83
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f693,plain,
    ( ~ r2_hidden(sK1,sK2(k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))))
    | ~ spl6_83 ),
    inference(unit_resulting_resolution,[],[f104,f683,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',t4_subset)).

fof(f683,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_83 ),
    inference(avatar_component_clause,[],[f682])).

fof(f104,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',existence_m1_subset_1)).

fof(f843,plain,
    ( ~ spl6_103
    | ~ spl6_40
    | spl6_83 ),
    inference(avatar_split_clause,[],[f692,f682,f298,f841])).

fof(f841,plain,
    ( spl6_103
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).

fof(f298,plain,
    ( spl6_40
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f692,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_40
    | ~ spl6_83 ),
    inference(unit_resulting_resolution,[],[f299,f683,f116])).

fof(f299,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f298])).

fof(f835,plain,
    ( ~ spl6_101
    | spl6_73
    | ~ spl6_98 ),
    inference(avatar_split_clause,[],[f828,f824,f540,f833])).

fof(f833,plain,
    ( spl6_101
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_tarski(sK2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f540,plain,
    ( spl6_73
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f824,plain,
    ( spl6_98
  <=> m1_subset_1(k1_tarski(sK2(sK1)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f828,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_tarski(sK2(sK1)))
    | ~ spl6_73
    | ~ spl6_98 ),
    inference(unit_resulting_resolution,[],[f541,f825,f116])).

fof(f825,plain,
    ( m1_subset_1(k1_tarski(sK2(sK1)),k1_zfmisc_1(sK1))
    | ~ spl6_98 ),
    inference(avatar_component_clause,[],[f824])).

fof(f541,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f540])).

fof(f826,plain,
    ( spl6_98
    | spl6_75 ),
    inference(avatar_split_clause,[],[f639,f543,f824])).

fof(f543,plain,
    ( spl6_75
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f639,plain,
    ( m1_subset_1(k1_tarski(sK2(sK1)),k1_zfmisc_1(sK1))
    | ~ spl6_75 ),
    inference(forward_demodulation,[],[f636,f637])).

fof(f637,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | ~ spl6_75 ),
    inference(unit_resulting_resolution,[],[f104,f544,f110])).

fof(f544,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl6_75 ),
    inference(avatar_component_clause,[],[f543])).

fof(f636,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK2(sK1)),k1_zfmisc_1(sK1))
    | ~ spl6_75 ),
    inference(unit_resulting_resolution,[],[f104,f544,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',dt_k6_domain_1)).

fof(f819,plain,
    ( ~ spl6_97
    | spl6_73 ),
    inference(avatar_split_clause,[],[f554,f540,f817])).

fof(f817,plain,
    ( spl6_97
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f554,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(k1_zfmisc_1(sK1)))
    | ~ spl6_73 ),
    inference(unit_resulting_resolution,[],[f104,f541,f116])).

fof(f812,plain,
    ( spl6_60
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_26
    | spl6_37
    | ~ spl6_56
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f809,f654,f440,f266,f220,f157,f143,f136,f129,f451])).

fof(f451,plain,
    ( spl6_60
  <=> r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f809,plain,
    ( r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_37
    | ~ spl6_56
    | ~ spl6_80 ),
    inference(forward_demodulation,[],[f808,f708])).

fof(f808,plain,
    ( r2_yellow_0(sK0,k4_waybel_0(sK0,k1_tarski(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_56
    | ~ spl6_80 ),
    inference(unit_resulting_resolution,[],[f130,f137,f144,f158,f655,f441,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,k4_waybel_0(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_yellow_0(X0,X1)
              | ~ r2_yellow_0(X0,k4_waybel_0(X0,X1)) )
            & ( r2_yellow_0(X0,k4_waybel_0(X0,X1))
              | ~ r2_yellow_0(X0,X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
          <=> r2_yellow_0(X0,k4_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
          <=> r2_yellow_0(X0,k4_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_yellow_0(X0,X1)
          <=> r2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',t37_waybel_0)).

fof(f811,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_26
    | spl6_37
    | ~ spl6_56
    | spl6_61
    | ~ spl6_80 ),
    inference(avatar_contradiction_clause,[],[f810])).

fof(f810,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_37
    | ~ spl6_56
    | ~ spl6_61
    | ~ spl6_80 ),
    inference(subsumption_resolution,[],[f809,f455])).

fof(f455,plain,
    ( ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f454])).

fof(f454,plain,
    ( spl6_61
  <=> ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f800,plain,
    ( spl6_94
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_26
    | spl6_37 ),
    inference(avatar_split_clause,[],[f783,f266,f220,f157,f150,f136,f129,f798])).

fof(f150,plain,
    ( spl6_6
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f783,plain,
    ( k2_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f776,f383])).

fof(f776,plain,
    ( k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f130,f137,f151,f158,f221,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',t39_yellow_0)).

fof(f151,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f766,plain,
    ( spl6_92
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_26
    | spl6_37 ),
    inference(avatar_split_clause,[],[f749,f266,f220,f157,f150,f136,f129,f764])).

fof(f764,plain,
    ( spl6_92
  <=> k1_yellow_0(sK0,k1_tarski(sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f749,plain,
    ( k1_yellow_0(sK0,k1_tarski(sK1)) = sK1
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f742,f383])).

fof(f742,plain,
    ( k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f130,f137,f151,f158,f221,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f737,plain,
    ( spl6_90
    | ~ spl6_16
    | spl6_19
    | ~ spl6_20
    | ~ spl6_24
    | spl6_39 ),
    inference(avatar_split_clause,[],[f573,f273,f213,f199,f192,f185,f735])).

fof(f735,plain,
    ( spl6_90
  <=> r2_yellow_0(sK5,k1_tarski(sK2(u1_struct_0(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f185,plain,
    ( spl6_16
  <=> l1_orders_2(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f192,plain,
    ( spl6_19
  <=> ~ v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f199,plain,
    ( spl6_20
  <=> v3_orders_2(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f213,plain,
    ( spl6_24
  <=> v5_orders_2(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f273,plain,
    ( spl6_39
  <=> ~ v1_xboole_0(u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f573,plain,
    ( r2_yellow_0(sK5,k1_tarski(sK2(u1_struct_0(sK5))))
    | ~ spl6_16
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_24
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f570,f385])).

fof(f385,plain,
    ( k6_domain_1(u1_struct_0(sK5),sK2(u1_struct_0(sK5))) = k1_tarski(sK2(u1_struct_0(sK5)))
    | ~ spl6_39 ),
    inference(unit_resulting_resolution,[],[f274,f104,f110])).

fof(f274,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f273])).

fof(f570,plain,
    ( r2_yellow_0(sK5,k6_domain_1(u1_struct_0(sK5),sK2(u1_struct_0(sK5))))
    | ~ spl6_16
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f193,f200,f214,f186,f104,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    inference(pure_predicate_removal,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',t38_yellow_0)).

fof(f186,plain,
    ( l1_orders_2(sK5)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f185])).

fof(f214,plain,
    ( v5_orders_2(sK5)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f213])).

fof(f200,plain,
    ( v3_orders_2(sK5)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f199])).

fof(f193,plain,
    ( ~ v2_struct_0(sK5)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f192])).

fof(f730,plain,
    ( spl6_88
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | spl6_37 ),
    inference(avatar_split_clause,[],[f574,f266,f157,f150,f136,f129,f728])).

fof(f728,plain,
    ( spl6_88
  <=> r2_yellow_0(sK0,k1_tarski(sK2(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_88])])).

fof(f574,plain,
    ( r2_yellow_0(sK0,k1_tarski(sK2(u1_struct_0(sK0))))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f569,f384])).

fof(f384,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) = k1_tarski(sK2(u1_struct_0(sK0)))
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f267,f104,f110])).

fof(f569,plain,
    ( r2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK2(u1_struct_0(sK0))))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f130,f137,f151,f158,f104,f97])).

fof(f722,plain,
    ( ~ spl6_87
    | spl6_83 ),
    inference(avatar_split_clause,[],[f694,f682,f720])).

fof(f720,plain,
    ( spl6_87
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f694,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_83 ),
    inference(unit_resulting_resolution,[],[f683,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',t1_subset)).

fof(f691,plain,
    ( ~ spl6_85
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f673,f561,f689])).

fof(f689,plain,
    ( spl6_85
  <=> ~ r2_hidden(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f561,plain,
    ( spl6_76
  <=> r2_hidden(sK2(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_76])])).

fof(f673,plain,
    ( ~ r2_hidden(sK1,sK2(sK1))
    | ~ spl6_76 ),
    inference(unit_resulting_resolution,[],[f562,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',antisymmetry_r2_hidden)).

fof(f562,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | ~ spl6_76 ),
    inference(avatar_component_clause,[],[f561])).

fof(f684,plain,
    ( ~ spl6_83
    | ~ spl6_10
    | ~ spl6_76 ),
    inference(avatar_split_clause,[],[f670,f561,f164,f682])).

fof(f164,plain,
    ( spl6_10
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f670,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_10
    | ~ spl6_76 ),
    inference(unit_resulting_resolution,[],[f165,f562,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',t5_subset)).

fof(f165,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f164])).

fof(f656,plain,
    ( spl6_80
    | spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_26
    | spl6_37 ),
    inference(avatar_split_clause,[],[f575,f266,f220,f157,f150,f136,f129,f654])).

fof(f575,plain,
    ( r2_yellow_0(sK0,k1_tarski(sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_26
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f568,f383])).

fof(f568,plain,
    ( r2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_26 ),
    inference(unit_resulting_resolution,[],[f130,f137,f151,f158,f221,f97])).

fof(f635,plain,
    ( spl6_78
    | ~ spl6_10
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f594,f546,f164,f633])).

fof(f633,plain,
    ( spl6_78
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f546,plain,
    ( spl6_74
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f594,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl6_10
    | ~ spl6_74 ),
    inference(unit_resulting_resolution,[],[f547,f249])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f247,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',t6_boole)).

fof(f247,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f165,f95])).

fof(f547,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f546])).

fof(f563,plain,
    ( spl6_76
    | spl6_75 ),
    inference(avatar_split_clause,[],[f551,f543,f561])).

fof(f551,plain,
    ( r2_hidden(sK2(sK1),sK1)
    | ~ spl6_75 ),
    inference(unit_resulting_resolution,[],[f104,f544,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',t2_subset)).

fof(f548,plain,
    ( ~ spl6_73
    | spl6_74
    | spl6_43 ),
    inference(avatar_split_clause,[],[f315,f312,f546,f540])).

fof(f312,plain,
    ( spl6_43
  <=> ~ r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f315,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl6_43 ),
    inference(resolution,[],[f313,f109])).

fof(f313,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f312])).

fof(f527,plain,
    ( ~ spl6_71
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f500,f447,f525])).

fof(f525,plain,
    ( spl6_71
  <=> ~ r2_hidden(u1_struct_0(sK5),sK2(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f447,plain,
    ( spl6_58
  <=> r2_hidden(sK2(u1_struct_0(sK5)),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f500,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),sK2(u1_struct_0(sK5)))
    | ~ spl6_58 ),
    inference(unit_resulting_resolution,[],[f448,f107])).

fof(f448,plain,
    ( r2_hidden(sK2(u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f447])).

fof(f517,plain,
    ( ~ spl6_69
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f431,f393,f515])).

fof(f515,plain,
    ( spl6_69
  <=> ~ r2_hidden(u1_struct_0(sK0),sK2(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f393,plain,
    ( spl6_54
  <=> r2_hidden(sK2(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f431,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK2(u1_struct_0(sK0)))
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f394,f107])).

fof(f394,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f393])).

fof(f487,plain,
    ( ~ spl6_67
    | spl6_65 ),
    inference(avatar_split_clause,[],[f479,f475,f485])).

fof(f485,plain,
    ( spl6_67
  <=> ~ r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f475,plain,
    ( spl6_65
  <=> ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f479,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_65 ),
    inference(unit_resulting_resolution,[],[f476,f108])).

fof(f476,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f475])).

fof(f477,plain,
    ( ~ spl6_65
    | ~ spl6_10
    | ~ spl6_16
    | spl6_39 ),
    inference(avatar_split_clause,[],[f463,f273,f185,f164,f475])).

fof(f463,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_10
    | ~ spl6_16
    | ~ spl6_39 ),
    inference(unit_resulting_resolution,[],[f165,f288,f117])).

fof(f288,plain,
    ( ! [X0] : r2_hidden(k2_yellow_0(sK5,X0),u1_struct_0(sK5))
    | ~ spl6_16
    | ~ spl6_39 ),
    inference(unit_resulting_resolution,[],[f280,f274,f109])).

fof(f280,plain,
    ( ! [X0] : m1_subset_1(k2_yellow_0(sK5,X0),u1_struct_0(sK5))
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f186,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',dt_k2_yellow_0)).

fof(f462,plain,
    ( ~ spl6_61
    | ~ spl6_63 ),
    inference(avatar_split_clause,[],[f92,f460,f454])).

fof(f92,plain,
    ( k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) != sK1
    | ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,
    ( ( k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) != sK1
      | ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f75,f74])).

fof(f74,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1
              | ~ r2_yellow_0(X0,k6_waybel_0(X0,X1)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k2_yellow_0(sK0,k6_waybel_0(sK0,X1)) != X1
            | ~ r2_yellow_0(sK0,k6_waybel_0(sK0,X1)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1
            | ~ r2_yellow_0(X0,k6_waybel_0(X0,X1)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( k2_yellow_0(X0,k6_waybel_0(X0,sK1)) != sK1
          | ~ r2_yellow_0(X0,k6_waybel_0(X0,sK1)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1
            | ~ r2_yellow_0(X0,k6_waybel_0(X0,X1)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1
            | ~ r2_yellow_0(X0,k6_waybel_0(X0,X1)) )
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
           => ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) = X1
              & r2_yellow_0(X0,k6_waybel_0(X0,X1)) ) ) ) ),
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
         => ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) = X1
            & r2_yellow_0(X0,k6_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',t39_waybel_0)).

fof(f449,plain,
    ( spl6_58
    | spl6_39 ),
    inference(avatar_split_clause,[],[f287,f273,f447])).

fof(f287,plain,
    ( r2_hidden(sK2(u1_struct_0(sK5)),u1_struct_0(sK5))
    | ~ spl6_39 ),
    inference(unit_resulting_resolution,[],[f104,f274,f109])).

fof(f442,plain,
    ( spl6_56
    | ~ spl6_26
    | spl6_37 ),
    inference(avatar_split_clause,[],[f415,f266,f220,f440])).

fof(f415,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_26
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f408,f383])).

fof(f408,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_26
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f267,f221,f111])).

fof(f395,plain,
    ( spl6_54
    | spl6_37 ),
    inference(avatar_split_clause,[],[f285,f266,f393])).

fof(f285,plain,
    ( r2_hidden(sK2(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f104,f267,f109])).

fof(f379,plain,
    ( ~ spl6_53
    | spl6_51 ),
    inference(avatar_split_clause,[],[f371,f367,f377])).

fof(f377,plain,
    ( spl6_53
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f367,plain,
    ( spl6_51
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f371,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_51 ),
    inference(unit_resulting_resolution,[],[f368,f108])).

fof(f368,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f367])).

fof(f369,plain,
    ( ~ spl6_51
    | ~ spl6_10
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f317,f298,f164,f367])).

fof(f317,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_10
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f299,f165,f117])).

fof(f361,plain,
    ( spl6_48
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f354,f351,f359])).

fof(f359,plain,
    ( spl6_48
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f351,plain,
    ( spl6_46
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f354,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_46 ),
    inference(superposition,[],[f104,f352])).

fof(f352,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f351])).

fof(f353,plain,
    ( spl6_46
    | ~ spl6_10
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f335,f326,f164,f351])).

fof(f326,plain,
    ( spl6_44
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f335,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_10
    | ~ spl6_44 ),
    inference(unit_resulting_resolution,[],[f327,f249])).

fof(f327,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f326])).

fof(f328,plain,
    ( spl6_44
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f320,f164,f326])).

fof(f320,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f104,f318,f109])).

fof(f318,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f165,f104,f117])).

fof(f314,plain,
    ( ~ spl6_43
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f303,f298,f312])).

fof(f303,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f299,f107])).

fof(f300,plain,
    ( spl6_40
    | ~ spl6_26
    | spl6_37 ),
    inference(avatar_split_clause,[],[f284,f266,f220,f298])).

fof(f284,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl6_26
    | ~ spl6_37 ),
    inference(unit_resulting_resolution,[],[f221,f267,f109])).

fof(f275,plain,
    ( ~ spl6_39
    | spl6_19
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f261,f244,f192,f273])).

fof(f244,plain,
    ( spl6_32
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f261,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK5))
    | ~ spl6_19
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f193,f245,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',fc2_struct_0)).

fof(f245,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f244])).

fof(f268,plain,
    ( ~ spl6_37
    | spl6_1
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f260,f230,f129,f266])).

fof(f230,plain,
    ( spl6_28
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f260,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_28 ),
    inference(unit_resulting_resolution,[],[f130,f231,f96])).

fof(f231,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f230])).

fof(f257,plain,
    ( spl6_34
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f247,f164,f255])).

fof(f255,plain,
    ( spl6_34
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f246,plain,
    ( spl6_32
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f225,f185,f244])).

fof(f225,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f186,f94])).

fof(f94,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',dt_l1_orders_2)).

fof(f239,plain,
    ( spl6_30
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f224,f178,f237])).

fof(f237,plain,
    ( spl6_30
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f178,plain,
    ( spl6_14
  <=> l1_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f224,plain,
    ( l1_struct_0(sK4)
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f179,f94])).

fof(f179,plain,
    ( l1_orders_2(sK4)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f178])).

fof(f232,plain,
    ( spl6_28
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f223,f157,f230])).

fof(f223,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f158,f94])).

fof(f222,plain,(
    spl6_26 ),
    inference(avatar_split_clause,[],[f91,f220])).

fof(f91,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f76])).

fof(f215,plain,(
    spl6_24 ),
    inference(avatar_split_clause,[],[f124,f213])).

fof(f124,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,
    ( v5_orders_2(sK5)
    & v4_orders_2(sK5)
    & v3_orders_2(sK5)
    & ~ v2_struct_0(sK5)
    & l1_orders_2(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f84])).

fof(f84,plain,
    ( ? [X0] :
        ( v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0)
        & l1_orders_2(X0) )
   => ( v5_orders_2(sK5)
      & v4_orders_2(sK5)
      & v3_orders_2(sK5)
      & ~ v2_struct_0(sK5)
      & l1_orders_2(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0)
      & l1_orders_2(X0) ) ),
    inference(pure_predicate_removal,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v2_orders_2(X0)
      & ~ v2_struct_0(X0)
      & l1_orders_2(X0) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,axiom,(
    ? [X0] :
      ( v3_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & v2_orders_2(X0)
      & ~ v2_struct_0(X0)
      & l1_orders_2(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',rc2_yellow_0)).

fof(f208,plain,(
    spl6_22 ),
    inference(avatar_split_clause,[],[f123,f206])).

fof(f206,plain,
    ( spl6_22
  <=> v4_orders_2(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f123,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f85])).

fof(f201,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f122,f199])).

fof(f122,plain,(
    v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f85])).

fof(f194,plain,(
    ~ spl6_19 ),
    inference(avatar_split_clause,[],[f121,f192])).

fof(f121,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f85])).

fof(f187,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f120,f185])).

fof(f120,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f85])).

fof(f180,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f119,f178])).

fof(f119,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    l1_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f82])).

fof(f82,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK4) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',existence_l1_orders_2)).

fof(f173,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f118,f171])).

fof(f171,plain,
    ( spl6_12
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f118,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    l1_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f80])).

fof(f80,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK3) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',existence_l1_struct_0)).

fof(f166,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f93,f164])).

fof(f93,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t39_waybel_0.p',dt_o_0_0_xboole_0)).

fof(f159,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f90,f157])).

fof(f90,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f152,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f89,f150])).

fof(f89,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f145,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f88,f143])).

fof(f88,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f138,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f87,f136])).

fof(f87,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f131,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f86,f129])).

fof(f86,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f76])).
%------------------------------------------------------------------------------
