%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:44 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 260 expanded)
%              Number of leaves         :   15 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :  182 ( 963 expanded)
%              Number of equality atoms :   19 (  97 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f547,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f494,f507,f540,f546])).

fof(f546,plain,(
    ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f28,f493])).

fof(f493,plain,
    ( u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f491])).

fof(f491,plain,
    ( spl6_7
  <=> u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f28,plain,(
    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

fof(f540,plain,(
    ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f523])).

fof(f523,plain,
    ( $false
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f69,f485,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f485,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f483])).

fof(f483,plain,
    ( spl6_5
  <=> v1_xboole_0(u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f69,plain,(
    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f26,f27,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f507,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f500])).

fof(f500,plain,
    ( $false
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f70,f69,f489,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f489,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),u1_pre_topc(sK0))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f487])).

fof(f487,plain,
    ( spl6_6
  <=> m1_subset_1(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f70,plain,(
    ~ v1_xboole_0(u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f69,f65])).

fof(f494,plain,
    ( spl6_5
    | ~ spl6_6
    | spl6_7 ),
    inference(avatar_split_clause,[],[f224,f491,f487,f483])).

fof(f224,plain,
    ( u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),u1_pre_topc(sK0))
    | v1_xboole_0(u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f223,f188])).

fof(f188,plain,(
    u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f105,f183,f31])).

fof(f31,plain,(
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

fof(f183,plain,(
    r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f112,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f112,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK0)))) ),
    inference(unit_resulting_resolution,[],[f73,f106,f62])).

fof(f106,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k3_tarski(u1_pre_topc(sK0)))) ),
    inference(unit_resulting_resolution,[],[f73,f65])).

fof(f73,plain,(
    r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK0)))) ),
    inference(unit_resulting_resolution,[],[f59,f69,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f59,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f105,plain,(
    r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f100,f33])).

fof(f33,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f100,plain,(
    r1_tarski(k3_tarski(u1_pre_topc(sK0)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f92,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f92,plain,(
    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f68,f54])).

fof(f68,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f223,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),u1_pre_topc(sK0))
    | v1_xboole_0(u1_pre_topc(sK0))
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f221,f188])).

fof(f221,plain,
    ( ~ m1_subset_1(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | v1_xboole_0(u1_pre_topc(sK0))
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(u1_pre_topc(sK0)) ),
    inference(resolution,[],[f78,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f78,plain,(
    ! [X2] :
      ( r2_hidden(X2,u1_pre_topc(sK0))
      | ~ m1_subset_1(X2,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f70,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:56:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (12106)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.21/0.52  % (12105)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.52  % (12107)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.21/0.52  % (12105)Refutation not found, incomplete strategy% (12105)------------------------------
% 1.21/0.52  % (12105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (12105)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.52  
% 1.21/0.52  % (12105)Memory used [KB]: 10746
% 1.21/0.52  % (12105)Time elapsed: 0.096 s
% 1.21/0.52  % (12105)------------------------------
% 1.21/0.52  % (12105)------------------------------
% 1.21/0.52  % (12123)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.21/0.52  % (12108)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.21/0.52  % (12110)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.21/0.53  % (12118)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.54  % (12114)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.36/0.54  % (12114)Refutation not found, incomplete strategy% (12114)------------------------------
% 1.36/0.54  % (12114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (12114)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (12114)Memory used [KB]: 10618
% 1.36/0.54  % (12114)Time elapsed: 0.118 s
% 1.36/0.54  % (12114)------------------------------
% 1.36/0.54  % (12114)------------------------------
% 1.36/0.54  % (12117)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.36/0.54  % (12115)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.54  % (12120)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.36/0.54  % (12104)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.54  % (12127)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.54  % (12131)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.54  % (12103)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.36/0.55  % (12107)Refutation found. Thanks to Tanya!
% 1.36/0.55  % SZS status Theorem for theBenchmark
% 1.36/0.55  % SZS output start Proof for theBenchmark
% 1.36/0.55  fof(f547,plain,(
% 1.36/0.55    $false),
% 1.36/0.55    inference(avatar_sat_refutation,[],[f494,f507,f540,f546])).
% 1.36/0.55  fof(f546,plain,(
% 1.36/0.55    ~spl6_7),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f542])).
% 1.36/0.55  fof(f542,plain,(
% 1.36/0.55    $false | ~spl6_7),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f28,f493])).
% 1.36/0.55  fof(f493,plain,(
% 1.36/0.55    u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | ~spl6_7),
% 1.36/0.55    inference(avatar_component_clause,[],[f491])).
% 1.36/0.55  fof(f491,plain,(
% 1.36/0.55    spl6_7 <=> u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.36/0.55  fof(f28,plain,(
% 1.36/0.55    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 1.36/0.55    inference(cnf_transformation,[],[f16])).
% 1.36/0.55  fof(f16,plain,(
% 1.36/0.55    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.36/0.55    inference(flattening,[],[f15])).
% 1.36/0.55  fof(f15,plain,(
% 1.36/0.55    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f13])).
% 1.36/0.55  fof(f13,negated_conjecture,(
% 1.36/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 1.36/0.55    inference(negated_conjecture,[],[f12])).
% 1.36/0.55  fof(f12,conjecture,(
% 1.36/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).
% 1.36/0.55  fof(f540,plain,(
% 1.36/0.55    ~spl6_5),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f523])).
% 1.36/0.55  fof(f523,plain,(
% 1.36/0.55    $false | ~spl6_5),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f69,f485,f65])).
% 1.36/0.55  fof(f65,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f1])).
% 1.36/0.55  fof(f1,axiom,(
% 1.36/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.36/0.55  fof(f485,plain,(
% 1.36/0.55    v1_xboole_0(u1_pre_topc(sK0)) | ~spl6_5),
% 1.36/0.55    inference(avatar_component_clause,[],[f483])).
% 1.36/0.55  fof(f483,plain,(
% 1.36/0.55    spl6_5 <=> v1_xboole_0(u1_pre_topc(sK0))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.36/0.55  fof(f69,plain,(
% 1.36/0.55    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f26,f27,f52])).
% 1.36/0.55  fof(f52,plain,(
% 1.36/0.55    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f21])).
% 1.36/0.55  fof(f21,plain,(
% 1.36/0.55    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.55    inference(flattening,[],[f20])).
% 1.36/0.55  fof(f20,plain,(
% 1.36/0.55    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f14])).
% 1.36/0.55  fof(f14,plain,(
% 1.36/0.55    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.36/0.55    inference(rectify,[],[f9])).
% 1.36/0.55  fof(f9,axiom,(
% 1.36/0.55    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 1.36/0.55  fof(f27,plain,(
% 1.36/0.55    l1_pre_topc(sK0)),
% 1.36/0.55    inference(cnf_transformation,[],[f16])).
% 1.36/0.55  fof(f26,plain,(
% 1.36/0.55    v2_pre_topc(sK0)),
% 1.36/0.55    inference(cnf_transformation,[],[f16])).
% 1.36/0.55  fof(f507,plain,(
% 1.36/0.55    spl6_6),
% 1.36/0.55    inference(avatar_contradiction_clause,[],[f500])).
% 1.36/0.55  fof(f500,plain,(
% 1.36/0.55    $false | spl6_6),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f70,f69,f489,f62])).
% 1.36/0.55  fof(f62,plain,(
% 1.36/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f24])).
% 1.36/0.55  fof(f24,plain,(
% 1.36/0.55    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f7])).
% 1.36/0.55  fof(f7,axiom,(
% 1.36/0.55    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.36/0.55  fof(f489,plain,(
% 1.36/0.55    ~m1_subset_1(u1_struct_0(sK0),u1_pre_topc(sK0)) | spl6_6),
% 1.36/0.55    inference(avatar_component_clause,[],[f487])).
% 1.36/0.55  fof(f487,plain,(
% 1.36/0.55    spl6_6 <=> m1_subset_1(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 1.36/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.36/0.55  fof(f70,plain,(
% 1.36/0.55    ~v1_xboole_0(u1_pre_topc(sK0))),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f69,f65])).
% 1.36/0.55  fof(f494,plain,(
% 1.36/0.55    spl6_5 | ~spl6_6 | spl6_7),
% 1.36/0.55    inference(avatar_split_clause,[],[f224,f491,f487,f483])).
% 1.36/0.55  fof(f224,plain,(
% 1.36/0.55    u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | ~m1_subset_1(u1_struct_0(sK0),u1_pre_topc(sK0)) | v1_xboole_0(u1_pre_topc(sK0))),
% 1.36/0.55    inference(forward_demodulation,[],[f223,f188])).
% 1.36/0.55  fof(f188,plain,(
% 1.36/0.55    u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f105,f183,f31])).
% 1.36/0.55  fof(f31,plain,(
% 1.36/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.36/0.55    inference(cnf_transformation,[],[f3])).
% 1.36/0.55  fof(f3,axiom,(
% 1.36/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.55  fof(f183,plain,(
% 1.36/0.55    r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f112,f54])).
% 1.36/0.55  fof(f54,plain,(
% 1.36/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f8])).
% 1.36/0.55  fof(f8,axiom,(
% 1.36/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.36/0.55  fof(f112,plain,(
% 1.36/0.55    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK0))))),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f73,f106,f62])).
% 1.36/0.55  fof(f106,plain,(
% 1.36/0.55    ~v1_xboole_0(k1_zfmisc_1(k3_tarski(u1_pre_topc(sK0))))),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f73,f65])).
% 1.36/0.55  fof(f73,plain,(
% 1.36/0.55    r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK0))))),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f59,f69,f55])).
% 1.36/0.55  fof(f55,plain,(
% 1.36/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f22])).
% 1.36/0.55  fof(f22,plain,(
% 1.36/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.36/0.55    inference(ennf_transformation,[],[f2])).
% 1.36/0.55  fof(f2,axiom,(
% 1.36/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.36/0.55  fof(f59,plain,(
% 1.36/0.55    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f4])).
% 1.36/0.55  fof(f4,axiom,(
% 1.36/0.55    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 1.36/0.55  fof(f105,plain,(
% 1.36/0.55    r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))),
% 1.36/0.55    inference(forward_demodulation,[],[f100,f33])).
% 1.36/0.55  fof(f33,plain,(
% 1.36/0.55    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.36/0.55    inference(cnf_transformation,[],[f6])).
% 1.36/0.55  fof(f6,axiom,(
% 1.36/0.55    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.36/0.55  fof(f100,plain,(
% 1.36/0.55    r1_tarski(k3_tarski(u1_pre_topc(sK0)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f92,f58])).
% 1.36/0.55  fof(f58,plain,(
% 1.36/0.55    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f23])).
% 1.36/0.55  fof(f23,plain,(
% 1.36/0.55    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 1.36/0.55    inference(ennf_transformation,[],[f5])).
% 1.36/0.55  fof(f5,axiom,(
% 1.36/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 1.36/0.55  fof(f92,plain,(
% 1.36/0.55    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f68,f54])).
% 1.36/0.55  fof(f68,plain,(
% 1.36/0.55    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.36/0.55    inference(unit_resulting_resolution,[],[f27,f34])).
% 1.36/0.55  fof(f34,plain,(
% 1.36/0.55    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f19])).
% 1.36/0.55  fof(f19,plain,(
% 1.36/0.55    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f10])).
% 1.36/0.55  fof(f10,axiom,(
% 1.36/0.55    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.36/0.55  fof(f223,plain,(
% 1.36/0.55    ~m1_subset_1(u1_struct_0(sK0),u1_pre_topc(sK0)) | v1_xboole_0(u1_pre_topc(sK0)) | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(u1_pre_topc(sK0))),
% 1.36/0.55    inference(forward_demodulation,[],[f221,f188])).
% 1.36/0.55  fof(f221,plain,(
% 1.36/0.55    ~m1_subset_1(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0)) | v1_xboole_0(u1_pre_topc(sK0)) | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(u1_pre_topc(sK0))),
% 1.36/0.55    inference(resolution,[],[f78,f32])).
% 1.36/0.55  fof(f32,plain,(
% 1.36/0.55    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))) )),
% 1.36/0.55    inference(cnf_transformation,[],[f18])).
% 1.36/0.55  fof(f18,plain,(
% 1.36/0.55    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 1.36/0.55    inference(flattening,[],[f17])).
% 1.36/0.55  fof(f17,plain,(
% 1.36/0.55    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 1.36/0.55    inference(ennf_transformation,[],[f11])).
% 1.36/0.55  fof(f11,axiom,(
% 1.36/0.55    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 1.36/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 1.36/0.55  fof(f78,plain,(
% 1.36/0.55    ( ! [X2] : (r2_hidden(X2,u1_pre_topc(sK0)) | ~m1_subset_1(X2,u1_pre_topc(sK0))) )),
% 1.36/0.55    inference(resolution,[],[f70,f63])).
% 1.36/0.55  fof(f63,plain,(
% 1.36/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 1.36/0.55    inference(cnf_transformation,[],[f24])).
% 1.36/0.55  % SZS output end Proof for theBenchmark
% 1.36/0.55  % (12107)------------------------------
% 1.36/0.55  % (12107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (12107)Termination reason: Refutation
% 1.36/0.55  
% 1.36/0.55  % (12107)Memory used [KB]: 6524
% 1.36/0.55  % (12107)Time elapsed: 0.131 s
% 1.36/0.55  % (12107)------------------------------
% 1.36/0.55  % (12107)------------------------------
% 1.36/0.55  % (12132)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.55  % (12130)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.55  % (12133)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.55  % (12116)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.55  % (12112)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.55  % (12099)Success in time 0.188 s
%------------------------------------------------------------------------------
