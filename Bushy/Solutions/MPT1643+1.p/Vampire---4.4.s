%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t23_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:46 EDT 2019

% Result     : Theorem 7.86s
% Output     : Refutation 7.86s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 337 expanded)
%              Number of leaves         :   10 (  88 expanded)
%              Depth                    :    9
%              Number of atoms          :  238 (1147 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2810,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f168,f196,f735,f2809])).

fof(f2809,plain,
    ( ~ spl14_0
    | spl14_3 ),
    inference(avatar_contradiction_clause,[],[f2803])).

fof(f2803,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f70,f161,f69,f738,f752,f974,f976,f975,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | r2_hidden(X3,X1)
      | ~ v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X3,X2)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X3,X2)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t23_waybel_0.p',d19_waybel_0)).

fof(f975,plain,
    ( r1_orders_2(sK0,sK2(k3_waybel_0(sK0,sK1),sK1),sK5(sK0,sK1,sK2(k3_waybel_0(sK0,sK1),sK1)))
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f70,f69,f129,f737,f752,f117])).

fof(f117,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,sK5(X0,X1,X3))
      | ~ r2_hidden(X3,k3_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_orders_2(X0,X3,sK5(X0,X1,X3))
      | ~ r2_hidden(X3,X2)
      | k3_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X3,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t23_waybel_0.p',d15_waybel_0)).

fof(f737,plain,
    ( r2_hidden(sK2(k3_waybel_0(sK0,sK1),sK1),k3_waybel_0(sK0,sK1))
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f164,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t23_waybel_0.p',d3_tarski)).

fof(f164,plain,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl14_3
  <=> ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f129,plain,(
    m1_subset_1(k3_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f70,f69,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t23_waybel_0.p',dt_k3_waybel_0)).

fof(f976,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2(k3_waybel_0(sK0,sK1),sK1)),u1_struct_0(sK0))
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f70,f69,f129,f737,f752,f118])).

fof(f118,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))
      | ~ r2_hidden(X3,k3_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_subset_1(sK5(X0,X1,X3),u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | k3_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f974,plain,
    ( r2_hidden(sK5(sK0,sK1,sK2(k3_waybel_0(sK0,sK1),sK1)),sK1)
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f70,f69,f129,f737,f752,f116])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k3_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k3_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f752,plain,
    ( m1_subset_1(sK2(k3_waybel_0(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f129,f737,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t23_waybel_0.p',t4_subset)).

fof(f738,plain,
    ( ~ r2_hidden(sK2(k3_waybel_0(sK0,sK1),sK1),sK1)
    | ~ spl14_3 ),
    inference(unit_resulting_resolution,[],[f164,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f69,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v12_waybel_0(X1,X0)
          <~> r1_tarski(k3_waybel_0(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v12_waybel_0(X1,X0)
            <=> r1_tarski(k3_waybel_0(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> r1_tarski(k3_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t23_waybel_0.p',t23_waybel_0)).

fof(f161,plain,
    ( v12_waybel_0(sK1,sK0)
    | ~ spl14_0 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl14_0
  <=> v12_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_0])])).

fof(f70,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f735,plain,
    ( spl14_1
    | ~ spl14_2 ),
    inference(avatar_contradiction_clause,[],[f733])).

fof(f733,plain,
    ( $false
    | ~ spl14_1
    | ~ spl14_2 ),
    inference(unit_resulting_resolution,[],[f70,f69,f198,f201,f199,f197,f129,f254,f115])).

fof(f115,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ m1_subset_1(k3_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X4)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k3_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,X4)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k3_waybel_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f254,plain,
    ( ~ r2_hidden(sK7(sK0,sK1),k3_waybel_0(sK0,sK1))
    | ~ spl14_1
    | ~ spl14_2 ),
    inference(unit_resulting_resolution,[],[f167,f200,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f200,plain,
    ( ~ r2_hidden(sK7(sK0,sK1),sK1)
    | ~ spl14_1 ),
    inference(unit_resulting_resolution,[],[f70,f69,f158,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(sK7(X0,X1),X1)
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f158,plain,
    ( ~ v12_waybel_0(sK1,sK0)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl14_1
  <=> ~ v12_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f167,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl14_2
  <=> r1_tarski(k3_waybel_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f197,plain,
    ( m1_subset_1(sK7(sK0,sK1),u1_struct_0(sK0))
    | ~ spl14_1 ),
    inference(unit_resulting_resolution,[],[f70,f69,f158,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f199,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1),sK6(sK0,sK1))
    | ~ spl14_1 ),
    inference(unit_resulting_resolution,[],[f70,f69,f158,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_orders_2(X0,sK7(X0,X1),sK6(X0,X1))
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f201,plain,
    ( m1_subset_1(sK6(sK0,sK1),u1_struct_0(sK0))
    | ~ spl14_1 ),
    inference(unit_resulting_resolution,[],[f70,f69,f158,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f198,plain,
    ( r2_hidden(sK6(sK0,sK1),sK1)
    | ~ spl14_1 ),
    inference(unit_resulting_resolution,[],[f70,f69,f158,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK6(X0,X1),X1)
      | v12_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f196,plain,
    ( ~ spl14_1
    | ~ spl14_3 ),
    inference(avatar_split_clause,[],[f68,f163,f157])).

fof(f68,plain,
    ( ~ r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | ~ v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f168,plain,
    ( spl14_0
    | spl14_2 ),
    inference(avatar_split_clause,[],[f67,f166,f160])).

fof(f67,plain,
    ( r1_tarski(k3_waybel_0(sK0,sK1),sK1)
    | v12_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
