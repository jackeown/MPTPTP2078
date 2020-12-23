%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 534 expanded)
%              Number of leaves         :   21 ( 120 expanded)
%              Depth                    :   12
%              Number of atoms          :  336 (2050 expanded)
%              Number of equality atoms :   18 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f284,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f132,f159,f212,f264,f283])).

fof(f283,plain,
    ( ~ spl6_1
    | ~ spl6_8 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f160,f87,f273,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f273,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl6_8 ),
    inference(backward_demodulation,[],[f120,f207])).

% (14687)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f207,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl6_8
  <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f120,plain,(
    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f93,f115,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f115,plain,(
    l1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f112,f67])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f112,plain,(
    l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f97,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f97,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f47,f46,f45,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f93,plain,(
    v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f46,f47,f45,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f87,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f47,f67])).

fof(f160,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f46,f47,f95,f97,f105,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v7_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

fof(f105,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_1
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f95,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f46,f45,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f264,plain,
    ( ~ spl6_1
    | spl6_2
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f108,f248,f249,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f249,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f45,f244,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f244,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f215,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f215,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1))),u1_struct_0(sK0))
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f211,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f211,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1)))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl6_9
  <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f248,plain,
    ( u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),sK1)
    | ~ spl6_1
    | spl6_9 ),
    inference(unit_resulting_resolution,[],[f161,f45,f244,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) != X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f161,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f87,f160,f72])).

fof(f108,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl6_2
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f212,plain,
    ( spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f129,f209,f205])).

fof(f129,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1)))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f113,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f113,plain,(
    r1_tarski(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f47,f97,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f159,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f122,f87,f147,f72])).

fof(f147,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | spl6_1 ),
    inference(backward_demodulation,[],[f120,f140])).

fof(f140,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f136,f137,f48])).

fof(f137,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1 ),
    inference(forward_demodulation,[],[f133,f134])).

fof(f134,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f47,f97,f104,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

% (14677)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f104,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f133,plain,
    ( m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f47,f97,f104,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f136,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | spl6_1 ),
    inference(backward_demodulation,[],[f135,f134])).

fof(f135,plain,
    ( ~ v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f47,f97,f104,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f122,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f46,f87,f45,f109,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(f109,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f132,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f44,f107,f103])).

fof(f44,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f110,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f43,f107,f103])).

fof(f43,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:49:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (14685)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (14676)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (14674)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (14696)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (14676)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f284,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f110,f132,f159,f212,f264,f283])).
% 0.22/0.53  fof(f283,plain,(
% 0.22/0.53    ~spl6_1 | ~spl6_8),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f279])).
% 0.22/0.53  fof(f279,plain,(
% 0.22/0.53    $false | (~spl6_1 | ~spl6_8)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f160,f87,f273,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0] : (v7_struct_0(X0) | ~l1_struct_0(X0) | ~v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.22/0.53  fof(f273,plain,(
% 0.22/0.53    v1_zfmisc_1(u1_struct_0(sK0)) | ~spl6_8),
% 0.22/0.53    inference(backward_demodulation,[],[f120,f207])).
% 0.22/0.53  % (14687)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~spl6_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f205])).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    spl6_8 <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f93,f115,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f112,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f47,f97,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f47,f46,f45,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.53    inference(negated_conjecture,[],[f17])).
% 0.22/0.53  fof(f17,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f46,f47,f45,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    l1_struct_0(sK0)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f47,f67])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    ~v7_struct_0(sK0) | ~spl6_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f46,f47,f95,f97,f105,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~v7_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~v1_tex_2(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl6_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f103])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    spl6_1 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f47,f46,f45,f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f264,plain,(
% 0.22/0.53    ~spl6_1 | spl6_2 | spl6_9),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f262])).
% 0.22/0.53  fof(f262,plain,(
% 0.22/0.53    $false | (~spl6_1 | spl6_2 | spl6_9)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f108,f248,f249,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_9),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f45,f244,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.53  fof(f244,plain,(
% 0.22/0.53    ~v1_xboole_0(u1_struct_0(sK0)) | spl6_9),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f215,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.53  fof(f215,plain,(
% 0.22/0.53    r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1))),u1_struct_0(sK0)) | spl6_9),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f211,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f211,plain,(
% 0.22/0.53    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1))) | spl6_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f209])).
% 0.22/0.53  fof(f209,plain,(
% 0.22/0.53    spl6_9 <=> r1_tarski(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.53  fof(f248,plain,(
% 0.22/0.53    u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),sK1) | (~spl6_1 | spl6_9)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f161,f45,f244,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) != X0 | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    ~v1_zfmisc_1(u1_struct_0(sK0)) | ~spl6_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f87,f160,f72])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl6_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f107])).
% 0.22/0.53  fof(f107,plain,(
% 0.22/0.53    spl6_2 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.53  fof(f212,plain,(
% 0.22/0.53    spl6_8 | ~spl6_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f129,f209,f205])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(k1_tex_2(sK0,sK1))) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f113,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    r1_tarski(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f47,f97,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    spl6_1 | ~spl6_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f155])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    $false | (spl6_1 | ~spl6_2)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f122,f87,f147,f72])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    v1_zfmisc_1(u1_struct_0(sK0)) | spl6_1),
% 0.22/0.53    inference(backward_demodulation,[],[f120,f140])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | spl6_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f136,f137,f48])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_1),
% 0.22/0.53    inference(forward_demodulation,[],[f133,f134])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | spl6_1),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f47,f97,f104,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tex_2(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  % (14677)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | spl6_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f103])).
% 0.22/0.54  fof(f133,plain,(
% 0.22/0.54    m1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_1),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f47,f97,f104,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tex_2(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | spl6_1),
% 0.22/0.54    inference(backward_demodulation,[],[f135,f134])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    ~v1_subset_1(sK2(sK0,k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | spl6_1),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f47,f97,f104,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    ~v7_struct_0(sK0) | ~spl6_2),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f46,f87,f45,f109,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,axiom,(
% 0.22/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).
% 0.22/0.54  fof(f109,plain,(
% 0.22/0.54    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl6_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f107])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    ~spl6_1 | ~spl6_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f44,f107,f103])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    spl6_1 | spl6_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f43,f107,f103])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (14676)------------------------------
% 0.22/0.54  % (14676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (14676)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (14676)Memory used [KB]: 6268
% 0.22/0.54  % (14676)Time elapsed: 0.111 s
% 0.22/0.54  % (14676)------------------------------
% 0.22/0.54  % (14676)------------------------------
% 0.22/0.54  % (14678)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.54  % (14666)Success in time 0.175 s
%------------------------------------------------------------------------------
