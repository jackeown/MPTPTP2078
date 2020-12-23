%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 250 expanded)
%              Number of leaves         :   13 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  252 (1553 expanded)
%              Number of equality atoms :   14 (  28 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f258,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f89,f127,f158,f231,f257])).

fof(f257,plain,
    ( ~ spl5_1
    | ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f240,f232,f59])).

fof(f59,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f232,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f34,f150])).

fof(f150,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl5_3
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f240,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f74,f150])).

fof(f74,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_1
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f231,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f206,f198,f59])).

fof(f198,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f34,f191])).

fof(f191,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f157,f186,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f186,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1),sK1)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f40,f33,f77,f34,f62,f183,f185,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f185,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK4(u1_struct_0(sK0),sK1))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f38,f39,f40,f35,f183,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,k3_yellow_0(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f183,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f157,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f62,plain,(
    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f40,f45])).

fof(f45,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f77,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_2
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f33,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f157,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl5_4
  <=> r2_hidden(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f206,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f74,f191])).

fof(f158,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f153,f155,f148])).

fof(f153,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(factoring,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,sK1),u1_struct_0(sK0))
      | r2_hidden(sK4(X0,sK1),X0)
      | sK1 = X0 ) ),
    inference(resolution,[],[f68,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f34,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f127,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f31,f78,f93,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f93,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | spl5_1 ),
    inference(backward_demodulation,[],[f62,f90])).

fof(f90,plain,
    ( sK1 = u1_struct_0(sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f34,f73,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f73,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f78,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f31,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f89,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f30,f76,f72])).

fof(f30,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f29,f76,f72])).

fof(f29,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:36:40 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.50  % (16893)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.51  % (16908)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.51  % (16916)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.51  % (16901)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.51  % (16896)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.52  % (16894)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (16897)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.52  % (16900)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (16899)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.52  % (16897)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % (16914)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.52  % (16917)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.52  % (16918)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.52  % (16895)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.53  % (16921)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.53  % (16919)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.53  % (16913)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.53  % (16907)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.53  % (16924)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.53  % (16909)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.53  % (16906)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.53  % (16912)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.53  % (16910)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.53  % (16915)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.53  % (16905)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.54  % (16904)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.54  % (16903)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.54  % (16902)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.54  % (16911)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.54  % (16902)Refutation not found, incomplete strategy% (16902)------------------------------
% 1.45/0.54  % (16902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (16902)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.54  
% 1.45/0.54  % (16902)Memory used [KB]: 10746
% 1.45/0.54  % (16902)Time elapsed: 0.140 s
% 1.45/0.54  % (16902)------------------------------
% 1.45/0.54  % (16902)------------------------------
% 1.45/0.54  % (16911)Refutation not found, incomplete strategy% (16911)------------------------------
% 1.45/0.54  % (16911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (16911)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.54  
% 1.45/0.54  % (16911)Memory used [KB]: 10746
% 1.45/0.54  % (16911)Time elapsed: 0.141 s
% 1.45/0.54  % (16911)------------------------------
% 1.45/0.54  % (16911)------------------------------
% 1.45/0.54  % SZS output start Proof for theBenchmark
% 1.45/0.54  fof(f258,plain,(
% 1.45/0.54    $false),
% 1.45/0.54    inference(avatar_sat_refutation,[],[f79,f89,f127,f158,f231,f257])).
% 1.45/0.54  fof(f257,plain,(
% 1.45/0.54    ~spl5_1 | ~spl5_3),
% 1.45/0.54    inference(avatar_contradiction_clause,[],[f252])).
% 1.45/0.54  fof(f252,plain,(
% 1.45/0.54    $false | (~spl5_1 | ~spl5_3)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f240,f232,f59])).
% 1.45/0.54  fof(f59,plain,(
% 1.45/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 1.45/0.54    inference(equality_resolution,[],[f47])).
% 1.45/0.54  fof(f47,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f23])).
% 1.45/0.54  fof(f23,plain,(
% 1.45/0.54    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f11])).
% 1.45/0.54  fof(f11,axiom,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.45/0.54  fof(f232,plain,(
% 1.45/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl5_3),
% 1.45/0.54    inference(backward_demodulation,[],[f34,f150])).
% 1.45/0.54  fof(f150,plain,(
% 1.45/0.54    sK1 = u1_struct_0(sK0) | ~spl5_3),
% 1.45/0.54    inference(avatar_component_clause,[],[f148])).
% 1.45/0.54  fof(f148,plain,(
% 1.45/0.54    spl5_3 <=> sK1 = u1_struct_0(sK0)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.45/0.54  fof(f34,plain,(
% 1.45/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.45/0.54    inference(cnf_transformation,[],[f15])).
% 1.45/0.54  fof(f15,plain,(
% 1.45/0.54    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.45/0.54    inference(flattening,[],[f14])).
% 1.45/0.54  fof(f14,plain,(
% 1.45/0.54    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f13])).
% 1.45/0.54  fof(f13,negated_conjecture,(
% 1.45/0.54    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.45/0.54    inference(negated_conjecture,[],[f12])).
% 1.45/0.54  fof(f12,conjecture,(
% 1.45/0.54    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.45/0.54  fof(f240,plain,(
% 1.45/0.54    v1_subset_1(sK1,sK1) | (~spl5_1 | ~spl5_3)),
% 1.45/0.54    inference(backward_demodulation,[],[f74,f150])).
% 1.45/0.54  fof(f74,plain,(
% 1.45/0.54    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_1),
% 1.45/0.54    inference(avatar_component_clause,[],[f72])).
% 1.45/0.54  fof(f72,plain,(
% 1.45/0.54    spl5_1 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.45/0.54  fof(f231,plain,(
% 1.45/0.54    ~spl5_1 | ~spl5_2 | ~spl5_4),
% 1.45/0.54    inference(avatar_contradiction_clause,[],[f226])).
% 1.45/0.54  fof(f226,plain,(
% 1.45/0.54    $false | (~spl5_1 | ~spl5_2 | ~spl5_4)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f206,f198,f59])).
% 1.45/0.54  fof(f198,plain,(
% 1.45/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl5_2 | ~spl5_4)),
% 1.45/0.54    inference(backward_demodulation,[],[f34,f191])).
% 1.45/0.54  fof(f191,plain,(
% 1.45/0.54    sK1 = u1_struct_0(sK0) | (~spl5_2 | ~spl5_4)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f157,f186,f56])).
% 1.45/0.54  fof(f56,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 1.45/0.54    inference(cnf_transformation,[],[f28])).
% 1.45/0.54  fof(f28,plain,(
% 1.45/0.54    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.45/0.54    inference(ennf_transformation,[],[f1])).
% 1.45/0.54  fof(f1,axiom,(
% 1.45/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.45/0.54  fof(f186,plain,(
% 1.45/0.54    r2_hidden(sK4(u1_struct_0(sK0),sK1),sK1) | (~spl5_2 | ~spl5_4)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f40,f33,f77,f34,f62,f183,f185,f52])).
% 1.45/0.54  fof(f52,plain,(
% 1.45/0.54    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f25])).
% 1.45/0.54  fof(f25,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.45/0.54    inference(flattening,[],[f24])).
% 1.45/0.54  fof(f24,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.45/0.54    inference(ennf_transformation,[],[f10])).
% 1.45/0.54  fof(f10,axiom,(
% 1.45/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.45/0.54  fof(f185,plain,(
% 1.45/0.54    r1_orders_2(sK0,k3_yellow_0(sK0),sK4(u1_struct_0(sK0),sK1)) | ~spl5_4),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f38,f39,f40,f35,f183,f44])).
% 1.45/0.54  fof(f44,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,k3_yellow_0(X0),X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f21])).
% 1.45/0.54  fof(f21,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.45/0.54    inference(flattening,[],[f20])).
% 1.45/0.54  fof(f20,plain,(
% 1.45/0.54    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f9])).
% 1.45/0.54  fof(f9,axiom,(
% 1.45/0.54    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).
% 1.45/0.54  fof(f35,plain,(
% 1.45/0.54    ~v2_struct_0(sK0)),
% 1.45/0.54    inference(cnf_transformation,[],[f15])).
% 1.45/0.54  fof(f39,plain,(
% 1.45/0.54    v1_yellow_0(sK0)),
% 1.45/0.54    inference(cnf_transformation,[],[f15])).
% 1.45/0.54  fof(f38,plain,(
% 1.45/0.54    v5_orders_2(sK0)),
% 1.45/0.54    inference(cnf_transformation,[],[f15])).
% 1.45/0.54  fof(f183,plain,(
% 1.45/0.54    m1_subset_1(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl5_4),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f157,f43])).
% 1.45/0.54  fof(f43,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f19])).
% 1.45/0.54  fof(f19,plain,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.45/0.54    inference(ennf_transformation,[],[f5])).
% 1.45/0.54  fof(f5,axiom,(
% 1.45/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.45/0.54  fof(f62,plain,(
% 1.45/0.54    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f40,f45])).
% 1.45/0.54  fof(f45,plain,(
% 1.45/0.54    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f22])).
% 1.45/0.54  fof(f22,plain,(
% 1.45/0.54    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.45/0.54    inference(ennf_transformation,[],[f8])).
% 1.45/0.54  fof(f8,axiom,(
% 1.45/0.54    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 1.45/0.54  fof(f77,plain,(
% 1.45/0.54    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl5_2),
% 1.45/0.54    inference(avatar_component_clause,[],[f76])).
% 1.45/0.54  fof(f76,plain,(
% 1.45/0.54    spl5_2 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.45/0.54  fof(f33,plain,(
% 1.45/0.54    v13_waybel_0(sK1,sK0)),
% 1.45/0.54    inference(cnf_transformation,[],[f15])).
% 1.45/0.54  fof(f40,plain,(
% 1.45/0.54    l1_orders_2(sK0)),
% 1.45/0.54    inference(cnf_transformation,[],[f15])).
% 1.45/0.54  fof(f157,plain,(
% 1.45/0.54    r2_hidden(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl5_4),
% 1.45/0.54    inference(avatar_component_clause,[],[f155])).
% 1.45/0.54  fof(f155,plain,(
% 1.45/0.54    spl5_4 <=> r2_hidden(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.45/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.45/0.54  fof(f206,plain,(
% 1.45/0.54    v1_subset_1(sK1,sK1) | (~spl5_1 | ~spl5_2 | ~spl5_4)),
% 1.45/0.54    inference(backward_demodulation,[],[f74,f191])).
% 1.45/0.54  fof(f158,plain,(
% 1.45/0.54    spl5_3 | spl5_4),
% 1.45/0.54    inference(avatar_split_clause,[],[f153,f155,f148])).
% 1.45/0.54  fof(f153,plain,(
% 1.45/0.54    r2_hidden(sK4(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 1.45/0.54    inference(factoring,[],[f88])).
% 1.45/0.54  fof(f88,plain,(
% 1.45/0.54    ( ! [X0] : (r2_hidden(sK4(X0,sK1),u1_struct_0(sK0)) | r2_hidden(sK4(X0,sK1),X0) | sK1 = X0) )),
% 1.45/0.54    inference(resolution,[],[f68,f55])).
% 1.45/0.54  fof(f55,plain,(
% 1.45/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 1.45/0.54    inference(cnf_transformation,[],[f28])).
% 1.45/0.54  fof(f68,plain,(
% 1.45/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,u1_struct_0(sK0))) )),
% 1.45/0.54    inference(resolution,[],[f34,f42])).
% 1.45/0.54  fof(f42,plain,(
% 1.45/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f18])).
% 1.45/0.54  fof(f18,plain,(
% 1.45/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.54    inference(ennf_transformation,[],[f4])).
% 1.45/0.54  fof(f4,axiom,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.45/0.54  fof(f127,plain,(
% 1.45/0.54    spl5_1 | spl5_2),
% 1.45/0.54    inference(avatar_contradiction_clause,[],[f121])).
% 1.45/0.54  fof(f121,plain,(
% 1.45/0.54    $false | (spl5_1 | spl5_2)),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f31,f78,f93,f54])).
% 1.45/0.54  fof(f54,plain,(
% 1.45/0.54    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f27])).
% 1.45/0.54  fof(f27,plain,(
% 1.45/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.45/0.54    inference(flattening,[],[f26])).
% 1.45/0.54  fof(f26,plain,(
% 1.45/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.45/0.54    inference(ennf_transformation,[],[f6])).
% 1.45/0.54  fof(f6,axiom,(
% 1.45/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.45/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.45/0.54  fof(f93,plain,(
% 1.45/0.54    m1_subset_1(k3_yellow_0(sK0),sK1) | spl5_1),
% 1.45/0.54    inference(backward_demodulation,[],[f62,f90])).
% 1.45/0.54  fof(f90,plain,(
% 1.45/0.54    sK1 = u1_struct_0(sK0) | spl5_1),
% 1.45/0.54    inference(unit_resulting_resolution,[],[f34,f73,f46])).
% 1.45/0.54  fof(f46,plain,(
% 1.45/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.45/0.54    inference(cnf_transformation,[],[f23])).
% 1.45/0.54  fof(f73,plain,(
% 1.45/0.54    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl5_1),
% 1.45/0.54    inference(avatar_component_clause,[],[f72])).
% 1.45/0.54  fof(f78,plain,(
% 1.45/0.54    ~r2_hidden(k3_yellow_0(sK0),sK1) | spl5_2),
% 1.45/0.54    inference(avatar_component_clause,[],[f76])).
% 1.45/0.54  fof(f31,plain,(
% 1.45/0.54    ~v1_xboole_0(sK1)),
% 1.45/0.54    inference(cnf_transformation,[],[f15])).
% 1.45/0.54  fof(f89,plain,(
% 1.45/0.54    ~spl5_1 | spl5_2),
% 1.45/0.54    inference(avatar_split_clause,[],[f30,f76,f72])).
% 1.45/0.54  fof(f30,plain,(
% 1.45/0.54    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.45/0.54    inference(cnf_transformation,[],[f15])).
% 1.45/0.54  fof(f79,plain,(
% 1.45/0.54    spl5_1 | ~spl5_2),
% 1.45/0.54    inference(avatar_split_clause,[],[f29,f76,f72])).
% 1.45/0.54  fof(f29,plain,(
% 1.45/0.54    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.45/0.54    inference(cnf_transformation,[],[f15])).
% 1.45/0.54  % SZS output end Proof for theBenchmark
% 1.45/0.54  % (16897)------------------------------
% 1.45/0.54  % (16897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (16897)Termination reason: Refutation
% 1.45/0.54  
% 1.45/0.54  % (16897)Memory used [KB]: 6268
% 1.45/0.54  % (16897)Time elapsed: 0.120 s
% 1.45/0.54  % (16897)------------------------------
% 1.45/0.54  % (16897)------------------------------
% 1.45/0.54  % (16920)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.55  % (16889)Success in time 0.195 s
%------------------------------------------------------------------------------
