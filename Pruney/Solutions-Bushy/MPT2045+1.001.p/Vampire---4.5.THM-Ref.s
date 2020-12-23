%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2045+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:05 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 582 expanded)
%              Number of leaves         :   16 ( 129 expanded)
%              Depth                    :   11
%              Number of atoms          :  355 (3283 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f113,f144,f240])).

fof(f240,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl7_1
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f90,f91,f171,f146,f180,f167,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X3,X0)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).

fof(f167,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3(k1_yellow19(sK0,sK1),sK2)),sK3(k1_yellow19(sK0,sK1),sK2))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f45,f151,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f151,plain,
    ( m1_subset_1(sK3(k1_yellow19(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f44,f45,f43,f42,f149,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f149,plain,
    ( m1_connsp_2(sK3(k1_yellow19(sK0,sK1),sK2),sK0,sK1)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f45,f44,f43,f42,f145,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_yellow19(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow19)).

fof(f145,plain,
    ( r2_hidden(sK3(k1_yellow19(sK0,sK1),sK2),k1_yellow19(sK0,sK1))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f104,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

% (11119)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (11110)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (11107)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (11104)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (11114)Refutation not found, incomplete strategy% (11114)------------------------------
% (11114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f104,plain,
    ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_2
  <=> r1_tarski(k1_yellow19(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f42,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <~> r1_tarski(k1_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <~> r1_tarski(k1_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
               => ( r2_waybel_7(X0,X2,X1)
                <=> r1_tarski(k1_yellow19(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
             => ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow19)).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f180,plain,
    ( r2_hidden(k1_tops_1(sK0,sK3(k1_yellow19(sK0,sK1),sK2)),sK2)
    | ~ spl7_1
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f45,f44,f101,f168,f170,f169,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r2_hidden(X2,X3)
      | r2_hidden(X3,X1)
      | ~ r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

% (11101)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0) )
               => r2_hidden(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_waybel_7)).

fof(f169,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3(k1_yellow19(sK0,sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f45,f151,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f170,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK3(k1_yellow19(sK0,sK1),sK2)),sK0)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f44,f45,f151,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f168,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3(k1_yellow19(sK0,sK1),sK2)))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f43,f44,f45,f42,f149,f151,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

% (11105)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (11114)Termination reason: Refutation not found, incomplete strategy

% (11114)Memory used [KB]: 10874
% (11114)Time elapsed: 0.096 s
% (11114)------------------------------
% (11114)------------------------------
% (11122)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f101,plain,
    ( r2_waybel_7(sK0,sK2,sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl7_1
  <=> r2_waybel_7(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f146,plain,
    ( ~ r2_hidden(sK3(k1_yellow19(sK0,sK1),sK2),sK2)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f104,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f171,plain,
    ( r1_tarski(sK3(k1_yellow19(sK0,sK1),sK2),u1_struct_0(sK0))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f151,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK0))))) ),
    inference(backward_demodulation,[],[f41,f88])).

fof(f88,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f72,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f72,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f45,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f17])).

fof(f90,plain,(
    v13_waybel_0(sK2,k3_yellow_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f40,f88])).

fof(f40,plain,(
    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f144,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | spl7_1
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f45,f44,f43,f42,f123,f119,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X2,k1_yellow19(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f119,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK1),k1_yellow19(sK0,sK1))
    | spl7_1
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f105,f117,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f117,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK1),sK2)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f45,f44,f100,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f100,plain,
    ( ~ r2_waybel_7(sK0,sK2,sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f105,plain,
    ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f123,plain,
    ( m1_connsp_2(sK4(sK0,sK2,sK1),sK0,sK1)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f43,f45,f44,f42,f116,f115,f114,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f114,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f45,f44,f100,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f115,plain,
    ( v3_pre_topc(sK4(sK0,sK2,sK1),sK0)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f45,f44,f100,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f116,plain,
    ( r2_hidden(sK1,sK4(sK0,sK2,sK1))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f45,f44,f100,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X2,sK4(X0,X1,X2))
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f113,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f39,f103,f99])).

fof(f39,plain,
    ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | ~ r2_waybel_7(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f106,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f38,f103,f99])).

fof(f38,plain,
    ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | r2_waybel_7(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
