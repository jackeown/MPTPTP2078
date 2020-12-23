%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t50_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:40:59 EDT 2019

% Result     : Theorem 7.78s
% Output     : Refutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 537 expanded)
%              Number of leaves         :   26 ( 139 expanded)
%              Depth                    :   13
%              Number of atoms          :  502 (2059 expanded)
%              Number of equality atoms :   44 (  75 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12780,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f177,f706,f710,f798,f802,f1128,f3648,f5495,f9955,f12002,f12777])).

fof(f12777,plain,
    ( spl9_1
    | ~ spl9_30
    | spl9_39
    | ~ spl9_52 ),
    inference(avatar_contradiction_clause,[],[f12745])).

fof(f12745,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_30
    | ~ spl9_39
    | ~ spl9_52 ),
    inference(unit_resulting_resolution,[],[f10229,f12632,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',t37_zfmisc_1)).

fof(f12632,plain,
    ( r2_hidden(sK2(sK1,k12_waybel_0(sK0,sK1)),k12_waybel_0(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_30
    | ~ spl9_39
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f12630,f10665])).

fof(f10665,plain,
    ( k2_yellow_0(sK0,k1_tarski(sK2(sK1,k12_waybel_0(sK0,sK1)))) = sK2(sK1,k12_waybel_0(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_30
    | ~ spl9_39 ),
    inference(backward_demodulation,[],[f10660,f10145])).

fof(f10145,plain,
    ( k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK1,k12_waybel_0(sK0,sK1)))) = sK2(sK1,k12_waybel_0(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f79,f9996,f1169])).

fof(f1169,plain,
    ( ! [X6,X7] :
        ( k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X6)) = X6
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X6,X7) )
    | ~ spl9_30 ),
    inference(resolution,[],[f1127,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',t4_subset)).

fof(f1127,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X3)) = X3 )
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f1126])).

fof(f1126,plain,
    ( spl9_30
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X3)) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f9996,plain,
    ( r2_hidden(sK2(sK1,k12_waybel_0(sK0,sK1)),sK1)
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f170,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',d3_tarski)).

fof(f170,plain,
    ( ~ r1_tarski(sK1,k12_waybel_0(sK0,sK1))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl9_1
  <=> ~ r1_tarski(sK1,k12_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f79,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k12_waybel_0(X0,X1))
            | ~ r1_tarski(X1,k11_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k12_waybel_0(X0,X1))
            | ~ r1_tarski(X1,k11_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r1_tarski(X1,k12_waybel_0(X0,X1))
              & r1_tarski(X1,k11_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r1_tarski(X1,k12_waybel_0(X0,X1))
            & r1_tarski(X1,k11_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',t50_waybel_0)).

fof(f10660,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK1,k12_waybel_0(sK0,sK1))) = k1_tarski(sK2(sK1,k12_waybel_0(sK0,sK1)))
    | ~ spl9_1
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f3576,f10138,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',redefinition_k6_domain_1)).

fof(f10138,plain,
    ( m1_subset_1(sK2(sK1,k12_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f79,f9996,f96])).

fof(f3576,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f3575])).

fof(f3575,plain,
    ( spl9_39
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f12630,plain,
    ( r2_hidden(k2_yellow_0(sK0,k1_tarski(sK2(sK1,k12_waybel_0(sK0,sK1)))),k12_waybel_0(sK0,sK1))
    | ~ spl9_1
    | ~ spl9_39
    | ~ spl9_52 ),
    inference(unit_resulting_resolution,[],[f79,f118,f10669,f10293,f12001])).

fof(f12001,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k2_yellow_0(sK0,X1),k12_waybel_0(sK0,X0))
        | ~ r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_finset_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f12000])).

fof(f12000,plain,
    ( spl9_52
  <=> ! [X1,X0] :
        ( r2_hidden(k2_yellow_0(sK0,X1),k12_waybel_0(sK0,X0))
        | ~ r2_yellow_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_finset_1(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f10293,plain,
    ( m1_subset_1(k1_tarski(sK2(sK1,k12_waybel_0(sK0,sK1))),k1_zfmisc_1(sK1))
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f10290,f10291])).

fof(f10291,plain,
    ( k6_domain_1(sK1,sK2(sK1,k12_waybel_0(sK0,sK1))) = k1_tarski(sK2(sK1,k12_waybel_0(sK0,sK1)))
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f217,f10140,f117])).

fof(f10140,plain,
    ( m1_subset_1(sK2(sK1,k12_waybel_0(sK0,sK1)),sK1)
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f9996,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',t1_subset)).

fof(f217,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f178,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',t7_boole)).

fof(f178,plain,
    ( r2_hidden(sK2(sK1,k12_waybel_0(sK0,sK1)),sK1)
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f170,f91])).

fof(f10290,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK2(sK1,k12_waybel_0(sK0,sK1))),k1_zfmisc_1(sK1))
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f217,f10140,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',dt_k6_domain_1)).

fof(f10669,plain,
    ( r2_yellow_0(sK0,k1_tarski(sK2(sK1,k12_waybel_0(sK0,sK1))))
    | ~ spl9_1
    | ~ spl9_39 ),
    inference(forward_demodulation,[],[f10656,f10660])).

fof(f10656,plain,
    ( r2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK1,k12_waybel_0(sK0,sK1))))
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f81,f82,f83,f80,f10138,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',t38_yellow_0)).

fof(f80,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f118,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',fc1_finset_1)).

fof(f10229,plain,
    ( ~ r1_tarski(k1_tarski(sK2(sK1,k12_waybel_0(sK0,sK1))),k12_waybel_0(sK0,sK1))
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f9997,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9997,plain,
    ( ~ r2_hidden(sK2(sK1,k12_waybel_0(sK0,sK1)),k12_waybel_0(sK0,sK1))
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f170,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12002,plain,
    ( spl9_10
    | ~ spl9_17
    | spl9_52
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f743,f704,f12000,f786,f649])).

fof(f649,plain,
    ( spl9_10
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f786,plain,
    ( spl9_17
  <=> ~ l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f704,plain,
    ( spl9_12
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k12_waybel_0(sK0,X1) = a_2_3_waybel_0(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f743,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k2_yellow_0(sK0,X1),k12_waybel_0(sK0,X0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_finset_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ r2_yellow_0(sK0,X1)
        | v2_struct_0(sK0) )
    | ~ spl9_12 ),
    inference(duplicate_literal_removal,[],[f742])).

fof(f742,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k2_yellow_0(sK0,X1),k12_waybel_0(sK0,X0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_finset_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ r2_yellow_0(sK0,X1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_12 ),
    inference(superposition,[],[f128,f705])).

fof(f705,plain,
    ( ! [X1] :
        ( k12_waybel_0(sK0,X1) = a_2_3_waybel_0(sK0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f704])).

fof(f128,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k2_yellow_0(X1,X3),a_2_3_waybel_0(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_finset_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ r2_yellow_0(X1,X3)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_finset_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k2_yellow_0(X1,X3) != X0
      | ~ r2_yellow_0(X1,X3)
      | r2_hidden(X0,a_2_3_waybel_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_3_waybel_0(X1,X2))
      <=> ? [X3] :
            ( r2_yellow_0(X1,X3)
            & k2_yellow_0(X1,X3) = X0
            & m1_subset_1(X3,k1_zfmisc_1(X2))
            & v1_finset_1(X3) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_3_waybel_0(X1,X2))
      <=> ? [X3] :
            ( r2_yellow_0(X1,X3)
            & k2_yellow_0(X1,X3) = X0
            & m1_subset_1(X3,k1_zfmisc_1(X2))
            & v1_finset_1(X3) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_3_waybel_0(X1,X2))
      <=> ? [X3] :
            ( r2_yellow_0(X1,X3)
            & k2_yellow_0(X1,X3) = X0
            & m1_subset_1(X3,k1_zfmisc_1(X2))
            & v1_finset_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',fraenkel_a_2_3_waybel_0)).

fof(f9955,plain,
    ( spl9_3
    | spl9_39 ),
    inference(avatar_contradiction_clause,[],[f9923])).

fof(f9923,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f6202,f9525,f88])).

fof(f9525,plain,
    ( r2_hidden(sK2(sK1,k11_waybel_0(sK0,sK1)),k11_waybel_0(sK0,sK1))
    | ~ spl9_3
    | ~ spl9_39 ),
    inference(forward_demodulation,[],[f9524,f6882])).

fof(f6882,plain,
    ( k1_yellow_0(sK0,k1_tarski(sK2(sK1,k11_waybel_0(sK0,sK1)))) = sK2(sK1,k11_waybel_0(sK0,sK1))
    | ~ spl9_3
    | ~ spl9_39 ),
    inference(forward_demodulation,[],[f6873,f6876])).

fof(f6876,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK1,k11_waybel_0(sK0,sK1))) = k1_tarski(sK2(sK1,k11_waybel_0(sK0,sK1)))
    | ~ spl9_3
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f3576,f6016,f117])).

fof(f6016,plain,
    ( m1_subset_1(sK2(sK1,k11_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f79,f5776,f96])).

fof(f5776,plain,
    ( r2_hidden(sK2(sK1,k11_waybel_0(sK0,sK1)),sK1)
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f176,f91])).

fof(f176,plain,
    ( ~ r1_tarski(sK1,k11_waybel_0(sK0,sK1))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl9_3
  <=> ~ r1_tarski(sK1,k11_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f6873,plain,
    ( k1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK1,k11_waybel_0(sK0,sK1)))) = sK2(sK1,k11_waybel_0(sK0,sK1))
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f81,f82,f83,f80,f6016,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',t39_yellow_0)).

fof(f9524,plain,
    ( r2_hidden(k1_yellow_0(sK0,k1_tarski(sK2(sK1,k11_waybel_0(sK0,sK1)))),k11_waybel_0(sK0,sK1))
    | ~ spl9_3
    | ~ spl9_39 ),
    inference(forward_demodulation,[],[f9515,f158])).

fof(f158,plain,(
    k11_waybel_0(sK0,sK1) = a_2_2_waybel_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f80,f83,f79,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k11_waybel_0(X0,X1) = a_2_2_waybel_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k11_waybel_0(X0,X1) = a_2_2_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k11_waybel_0(X0,X1) = a_2_2_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k11_waybel_0(X0,X1) = a_2_2_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',d27_waybel_0)).

fof(f9515,plain,
    ( r2_hidden(k1_yellow_0(sK0,k1_tarski(sK2(sK1,k11_waybel_0(sK0,sK1)))),a_2_2_waybel_0(sK0,sK1))
    | ~ spl9_3
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f83,f80,f79,f6884,f118,f6379,f129])).

fof(f129,plain,(
    ! [X2,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_finset_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ r1_yellow_0(X1,X3)
      | r2_hidden(k1_yellow_0(X1,X3),a_2_2_waybel_0(X1,X2)) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v1_finset_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k1_yellow_0(X1,X3) != X0
      | ~ r1_yellow_0(X1,X3)
      | r2_hidden(X0,a_2_2_waybel_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_waybel_0(X1,X2))
      <=> ? [X3] :
            ( r1_yellow_0(X1,X3)
            & k1_yellow_0(X1,X3) = X0
            & m1_subset_1(X3,k1_zfmisc_1(X2))
            & v1_finset_1(X3) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_waybel_0(X1,X2))
      <=> ? [X3] :
            ( r1_yellow_0(X1,X3)
            & k1_yellow_0(X1,X3) = X0
            & m1_subset_1(X3,k1_zfmisc_1(X2))
            & v1_finset_1(X3) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_2_waybel_0(X1,X2))
      <=> ? [X3] :
            ( r1_yellow_0(X1,X3)
            & k1_yellow_0(X1,X3) = X0
            & m1_subset_1(X3,k1_zfmisc_1(X2))
            & v1_finset_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',fraenkel_a_2_2_waybel_0)).

fof(f6379,plain,
    ( m1_subset_1(k1_tarski(sK2(sK1,k11_waybel_0(sK0,sK1))),k1_zfmisc_1(sK1))
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f6376,f6377])).

fof(f6377,plain,
    ( k6_domain_1(sK1,sK2(sK1,k11_waybel_0(sK0,sK1))) = k1_tarski(sK2(sK1,k11_waybel_0(sK0,sK1)))
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f1860,f6017,f117])).

fof(f6017,plain,
    ( m1_subset_1(sK2(sK1,k11_waybel_0(sK0,sK1)),sK1)
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f5776,f98])).

fof(f1860,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f1834,f115])).

fof(f1834,plain,
    ( r2_hidden(sK2(sK1,k11_waybel_0(sK0,sK1)),sK1)
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f176,f91])).

fof(f6376,plain,
    ( m1_subset_1(k6_domain_1(sK1,sK2(sK1,k11_waybel_0(sK0,sK1))),k1_zfmisc_1(sK1))
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f1860,f6017,f126])).

fof(f6884,plain,
    ( r1_yellow_0(sK0,k1_tarski(sK2(sK1,k11_waybel_0(sK0,sK1))))
    | ~ spl9_3
    | ~ spl9_39 ),
    inference(forward_demodulation,[],[f6871,f6876])).

fof(f6871,plain,
    ( r1_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK1,k11_waybel_0(sK0,sK1))))
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f81,f82,f83,f80,f6016,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f6202,plain,
    ( ~ r1_tarski(k1_tarski(sK2(sK1,k11_waybel_0(sK0,sK1))),k11_waybel_0(sK0,sK1))
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f5777,f89])).

fof(f5777,plain,
    ( ~ r2_hidden(sK2(sK1,k11_waybel_0(sK0,sK1)),k11_waybel_0(sK0,sK1))
    | ~ spl9_3 ),
    inference(unit_resulting_resolution,[],[f176,f92])).

fof(f5495,plain,
    ( spl9_1
    | ~ spl9_38 ),
    inference(avatar_contradiction_clause,[],[f5452])).

fof(f5452,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f214,f3579])).

fof(f3579,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f3578])).

fof(f3578,plain,
    ( spl9_38
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f214,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl9_1 ),
    inference(unit_resulting_resolution,[],[f79,f178,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',t5_subset)).

fof(f3648,plain,
    ( spl9_3
    | ~ spl9_38 ),
    inference(avatar_contradiction_clause,[],[f3634])).

fof(f3634,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f1834,f79,f3579,f95])).

fof(f1128,plain,
    ( spl9_30
    | ~ spl9_17
    | spl9_10
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f138,f792,f649,f786,f1126])).

fof(f792,plain,
    ( spl9_19
  <=> ~ v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f138,plain,(
    ! [X3] :
      ( ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),X3)) = X3 ) ),
    inference(resolution,[],[f82,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f802,plain,(
    spl9_19 ),
    inference(avatar_contradiction_clause,[],[f799])).

fof(f799,plain,
    ( $false
    | ~ spl9_19 ),
    inference(unit_resulting_resolution,[],[f81,f793])).

fof(f793,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f792])).

fof(f798,plain,(
    spl9_17 ),
    inference(avatar_contradiction_clause,[],[f795])).

fof(f795,plain,
    ( $false
    | ~ spl9_17 ),
    inference(unit_resulting_resolution,[],[f83,f787])).

fof(f787,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f786])).

fof(f710,plain,(
    ~ spl9_10 ),
    inference(avatar_contradiction_clause,[],[f707])).

fof(f707,plain,
    ( $false
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f80,f650])).

fof(f650,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f649])).

fof(f706,plain,
    ( spl9_12
    | spl9_10 ),
    inference(avatar_split_clause,[],[f154,f649,f704])).

fof(f154,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k12_waybel_0(sK0,X1) = a_2_3_waybel_0(sK0,X1) ) ),
    inference(resolution,[],[f83,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k12_waybel_0(X0,X1) = a_2_3_waybel_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k12_waybel_0(X0,X1) = a_2_3_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k12_waybel_0(X0,X1) = a_2_3_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k12_waybel_0(X0,X1) = a_2_3_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t50_waybel_0.p',d28_waybel_0)).

fof(f177,plain,
    ( ~ spl9_1
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f78,f175,f169])).

fof(f78,plain,
    ( ~ r1_tarski(sK1,k11_waybel_0(sK0,sK1))
    | ~ r1_tarski(sK1,k12_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
