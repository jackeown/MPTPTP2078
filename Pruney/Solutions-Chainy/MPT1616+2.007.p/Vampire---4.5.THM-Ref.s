%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 127 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  187 ( 431 expanded)
%              Number of equality atoms :   23 (  56 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f155,f178,f238,f273,f284])).

fof(f284,plain,
    ( ~ spl9_3
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f26,f275])).

fof(f275,plain,
    ( u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | ~ spl9_3
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f150,f173])).

fof(f173,plain,
    ( u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl9_5
  <=> u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f150,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(u1_pre_topc(sK0))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl9_3
  <=> k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f26,plain,(
    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

fof(f273,plain,
    ( spl9_4
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | spl9_4
    | ~ spl9_5 ),
    inference(unit_resulting_resolution,[],[f71,f68,f249,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f249,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | spl9_4
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f154,f173])).

fof(f154,plain,
    ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | spl9_4 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl9_4
  <=> r2_hidden(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f71,plain,(
    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f24,f25,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(rectify,[],[f8])).

fof(f8,axiom,(
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

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

% (9566)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f24,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f238,plain,(
    spl9_6 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl9_6 ),
    inference(unit_resulting_resolution,[],[f71,f180,f181,f65])).

fof(f65,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k3_tarski(X0))
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X3) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f181,plain,
    ( ~ r2_hidden(sK7(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))),k3_tarski(u1_pre_topc(sK0)))
    | spl9_6 ),
    inference(unit_resulting_resolution,[],[f177,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f177,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))
    | spl9_6 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl9_6
  <=> r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f180,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))),u1_struct_0(sK0))
    | spl9_6 ),
    inference(unit_resulting_resolution,[],[f177,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f178,plain,
    ( spl9_5
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f102,f175,f171])).

fof(f102,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))
    | u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) ),
    inference(resolution,[],[f89,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f89,plain,(
    r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f83,f36])).

fof(f36,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f83,plain,(
    r1_tarski(k3_tarski(u1_pre_topc(sK0)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f81,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f81,plain,(
    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f70,f62])).

% (9570)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f70,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f25,f38])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f155,plain,
    ( spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f76,f152,f148])).

fof(f76,plain,
    ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(u1_pre_topc(sK0)) ),
    inference(resolution,[],[f72,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f72,plain,(
    ~ v1_xboole_0(u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f71,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:12:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (9565)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (9571)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (9571)Refutation not found, incomplete strategy% (9571)------------------------------
% 0.21/0.50  % (9571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (9571)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (9571)Memory used [KB]: 10618
% 0.21/0.50  % (9571)Time elapsed: 0.092 s
% 0.21/0.50  % (9571)------------------------------
% 0.21/0.50  % (9571)------------------------------
% 0.21/0.51  % (9567)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (9587)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (9565)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f285,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f155,f178,f238,f273,f284])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    ~spl9_3 | ~spl9_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f280])).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    $false | (~spl9_3 | ~spl9_5)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f26,f275])).
% 0.21/0.51  fof(f275,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | (~spl9_3 | ~spl9_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f150,f173])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) | ~spl9_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f171])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    spl9_5 <=> u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(u1_pre_topc(sK0)) | ~spl9_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f148])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    spl9_3 <=> k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(u1_pre_topc(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.21/0.51    inference(negated_conjecture,[],[f11])).
% 0.21/0.51  fof(f11,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    spl9_4 | ~spl9_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f266])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    $false | (spl9_4 | ~spl9_5)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f71,f68,f249,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    ~r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | (spl9_4 | ~spl9_5)),
% 0.21/0.51    inference(backward_demodulation,[],[f154,f173])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    ~r2_hidden(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0)) | spl9_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f152])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    spl9_4 <=> r2_hidden(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f24,f25,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.51    inference(rectify,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  % (9566)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    spl9_6),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f233])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    $false | spl9_6),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f71,f180,f181,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X2,X0,X3] : (r2_hidden(X2,k3_tarski(X0)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) )),
% 0.21/0.51    inference(equality_resolution,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    ~r2_hidden(sK7(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))),k3_tarski(u1_pre_topc(sK0))) | spl9_6),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f177,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    ~r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) | spl9_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f175])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    spl9_6 <=> r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    r2_hidden(sK7(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))),u1_struct_0(sK0)) | spl9_6),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f177,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    spl9_5 | ~spl9_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f102,f175,f171])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ~r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) | u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))),
% 0.21/0.51    inference(resolution,[],[f89,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))),
% 0.21/0.51    inference(forward_demodulation,[],[f83,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    r1_tarski(k3_tarski(u1_pre_topc(sK0)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f81,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f70,f62])).
% 0.21/0.51  % (9570)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f25,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    spl9_3 | ~spl9_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f76,f152,f148])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ~r2_hidden(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0)) | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) = k3_tarski(u1_pre_topc(sK0))),
% 0.21/0.51    inference(resolution,[],[f72,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (v1_xboole_0(X0) | ~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ~v1_xboole_0(u1_pre_topc(sK0))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f71,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (9565)------------------------------
% 0.21/0.51  % (9565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9565)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (9565)Memory used [KB]: 6396
% 0.21/0.51  % (9565)Time elapsed: 0.111 s
% 0.21/0.51  % (9565)------------------------------
% 0.21/0.51  % (9565)------------------------------
% 0.21/0.52  % (9584)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (9560)Success in time 0.161 s
%------------------------------------------------------------------------------
