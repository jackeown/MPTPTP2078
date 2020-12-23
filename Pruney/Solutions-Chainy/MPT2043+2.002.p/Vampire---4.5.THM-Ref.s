%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 150 expanded)
%              Number of leaves         :   13 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  170 ( 443 expanded)
%              Number of equality atoms :   19 (  62 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f377,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f252,f347,f376])).

fof(f376,plain,(
    ~ spl8_1 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f351,f350,f71])).

fof(f71,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f51,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f350,plain,
    ( m1_subset_1(sK1,k9_setfam_1(sK1))
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f74,f247])).

fof(f247,plain,
    ( sK1 = k9_setfam_1(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl8_1
  <=> sK1 = k9_setfam_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f74,plain,(
    m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) ),
    inference(forward_demodulation,[],[f52,f49])).

fof(f49,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f52,plain,(
    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))))) ),
    inference(definition_unfolding,[],[f25,f51,f43])).

fof(f43,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( v1_xboole_0(X2)
              & r2_hidden(X2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
          & v13_waybel_0(X1,k3_yellow_1(X0))
          & v2_waybel_0(X1,k3_yellow_1(X0))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
              & v13_waybel_0(X1,k3_yellow_1(X0))
              & v2_waybel_0(X1,k3_yellow_1(X0))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ~ ( v1_xboole_0(X2)
                  & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
            & v13_waybel_0(X1,k3_yellow_1(X0))
            & v2_waybel_0(X1,k3_yellow_1(X0))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ~ ( v1_xboole_0(X2)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).

fof(f351,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f75,f247])).

fof(f75,plain,(
    v1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(forward_demodulation,[],[f55,f49])).

fof(f55,plain,(
    v1_subset_1(sK1,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))) ),
    inference(definition_unfolding,[],[f22,f43])).

fof(f22,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f347,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f149,f340,f61])).

% (25690)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f34,f51])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f340,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))
    | spl8_2 ),
    inference(forward_demodulation,[],[f330,f49])).

fof(f330,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f19,f53,f255,f86,f321,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X3,X0)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0))) ) ),
    inference(definition_unfolding,[],[f36,f51,f43,f43])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X3,X0)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_7)).

fof(f321,plain,
    ( r1_tarski(sK4(k9_setfam_1(sK0),sK1),sK0)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f254,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k9_setfam_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k9_setfam_1(X0) != X1 ) ),
    inference(definition_unfolding,[],[f28,f51])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f254,plain,
    ( r2_hidden(sK4(k9_setfam_1(sK0),sK1),k9_setfam_1(sK0))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f251,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f251,plain,
    ( ~ r1_tarski(k9_setfam_1(sK0),sK1)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl8_2
  <=> r1_tarski(k9_setfam_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f86,plain,(
    ! [X0] : r1_tarski(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f76,f32])).

fof(f76,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f20,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f20,plain,(
    v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f255,plain,
    ( ~ r2_hidden(sK4(k9_setfam_1(sK0),sK1),sK1)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f251,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    v13_waybel_0(sK1,k2_yellow_1(k9_setfam_1(sK0))) ),
    inference(definition_unfolding,[],[f24,f43])).

fof(f24,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f149,plain,(
    r1_tarski(sK1,k9_setfam_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f74,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f51])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f252,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f156,f249,f245])).

fof(f156,plain,
    ( ~ r1_tarski(k9_setfam_1(sK0),sK1)
    | sK1 = k9_setfam_1(sK0) ),
    inference(resolution,[],[f149,f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:28:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (25696)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.50  % (25688)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (25677)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (25698)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (25682)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (25678)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (25680)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (25678)Refutation not found, incomplete strategy% (25678)------------------------------
% 0.20/0.54  % (25678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25678)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25678)Memory used [KB]: 10746
% 0.20/0.54  % (25678)Time elapsed: 0.143 s
% 0.20/0.54  % (25678)------------------------------
% 0.20/0.54  % (25678)------------------------------
% 0.20/0.54  % (25698)Refutation not found, incomplete strategy% (25698)------------------------------
% 0.20/0.54  % (25698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25698)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25698)Memory used [KB]: 10746
% 0.20/0.54  % (25698)Time elapsed: 0.093 s
% 0.20/0.54  % (25698)------------------------------
% 0.20/0.54  % (25698)------------------------------
% 0.20/0.55  % (25676)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.55  % (25687)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (25686)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (25700)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.56  % (25685)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.56  % (25701)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (25679)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.56  % (25691)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.56  % (25681)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.56  % (25680)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f377,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f252,f347,f376])).
% 0.20/0.56  fof(f376,plain,(
% 0.20/0.56    ~spl8_1),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f372])).
% 0.20/0.56  fof(f372,plain,(
% 0.20/0.56    $false | ~spl8_1),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f351,f350,f71])).
% 0.20/0.56  fof(f71,plain,(
% 0.20/0.56    ( ! [X1] : (~m1_subset_1(X1,k9_setfam_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.20/0.56    inference(equality_resolution,[],[f67])).
% 0.20/0.56  fof(f67,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k9_setfam_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f42,f51])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.56  fof(f350,plain,(
% 0.20/0.56    m1_subset_1(sK1,k9_setfam_1(sK1)) | ~spl8_1),
% 0.20/0.56    inference(backward_demodulation,[],[f74,f247])).
% 0.20/0.56  fof(f247,plain,(
% 0.20/0.56    sK1 = k9_setfam_1(sK0) | ~spl8_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f245])).
% 0.20/0.56  fof(f245,plain,(
% 0.20/0.56    spl8_1 <=> sK1 = k9_setfam_1(sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.56  fof(f74,plain,(
% 0.20/0.56    m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))),
% 0.20/0.56    inference(forward_demodulation,[],[f52,f49])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))))),
% 0.20/0.56    inference(definition_unfolding,[],[f25,f51,f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.56    inference(flattening,[],[f13])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,negated_conjecture,(
% 0.20/0.56    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.20/0.56    inference(negated_conjecture,[],[f11])).
% 0.20/0.56  fof(f11,conjecture,(
% 0.20/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
% 0.20/0.56  fof(f351,plain,(
% 0.20/0.56    v1_subset_1(sK1,sK1) | ~spl8_1),
% 0.20/0.56    inference(backward_demodulation,[],[f75,f247])).
% 0.20/0.56  fof(f75,plain,(
% 0.20/0.56    v1_subset_1(sK1,k9_setfam_1(sK0))),
% 0.20/0.56    inference(forward_demodulation,[],[f55,f49])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    v1_subset_1(sK1,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))))),
% 0.20/0.56    inference(definition_unfolding,[],[f22,f43])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f347,plain,(
% 0.20/0.56    spl8_2),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f343])).
% 0.20/0.56  fof(f343,plain,(
% 0.20/0.56    $false | spl8_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f149,f340,f61])).
% 0.20/0.56  % (25690)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k9_setfam_1(X1))) )),
% 0.20/0.56    inference(definition_unfolding,[],[f34,f51])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.56  fof(f340,plain,(
% 0.20/0.56    ~m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) | spl8_2),
% 0.20/0.56    inference(forward_demodulation,[],[f330,f49])).
% 0.20/0.56  fof(f330,plain,(
% 0.20/0.56    ~m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))))) | spl8_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f19,f53,f255,f86,f321,f66])).
% 0.20/0.56  fof(f66,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,X0) | ~r2_hidden(X2,X1) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0)))) )),
% 0.20/0.56    inference(definition_unfolding,[],[f36,f51,f43,f43])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,X0) | ~r2_hidden(X2,X1) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,k3_yellow_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.20/0.56    inference(flattening,[],[f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | (~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.20/0.56    inference(ennf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,axiom,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) => (v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : ((r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => r2_hidden(X3,X1))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_7)).
% 0.20/0.56  fof(f321,plain,(
% 0.20/0.56    r1_tarski(sK4(k9_setfam_1(sK0),sK1),sK0) | spl8_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f254,f69])).
% 0.20/0.56  fof(f69,plain,(
% 0.20/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k9_setfam_1(X0)) | r1_tarski(X2,X0)) )),
% 0.20/0.56    inference(equality_resolution,[],[f58])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k9_setfam_1(X0) != X1) )),
% 0.20/0.56    inference(definition_unfolding,[],[f28,f51])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.56  fof(f254,plain,(
% 0.20/0.56    r2_hidden(sK4(k9_setfam_1(sK0),sK1),k9_setfam_1(sK0)) | spl8_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f251,f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.56  fof(f251,plain,(
% 0.20/0.56    ~r1_tarski(k9_setfam_1(sK0),sK1) | spl8_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f249])).
% 0.20/0.56  fof(f249,plain,(
% 0.20/0.56    spl8_2 <=> r1_tarski(k9_setfam_1(sK0),sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(sK2,X0)) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f76,f32])).
% 0.20/0.56  fof(f76,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK2)) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f20,f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    v1_xboole_0(sK2)),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f255,plain,(
% 0.20/0.56    ~r2_hidden(sK4(k9_setfam_1(sK0),sK1),sK1) | spl8_2),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f251,f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    v13_waybel_0(sK1,k2_yellow_1(k9_setfam_1(sK0)))),
% 0.20/0.57    inference(definition_unfolding,[],[f24,f43])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    v13_waybel_0(sK1,k3_yellow_1(sK0))),
% 0.20/0.57    inference(cnf_transformation,[],[f14])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    r2_hidden(sK2,sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f14])).
% 0.20/0.57  fof(f149,plain,(
% 0.20/0.57    r1_tarski(sK1,k9_setfam_1(sK0))),
% 0.20/0.57    inference(unit_resulting_resolution,[],[f74,f60])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k9_setfam_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f35,f51])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f252,plain,(
% 0.20/0.57    spl8_1 | ~spl8_2),
% 0.20/0.57    inference(avatar_split_clause,[],[f156,f249,f245])).
% 0.20/0.57  fof(f156,plain,(
% 0.20/0.57    ~r1_tarski(k9_setfam_1(sK0),sK1) | sK1 = k9_setfam_1(sK0)),
% 0.20/0.57    inference(resolution,[],[f149,f48])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (25680)------------------------------
% 0.20/0.57  % (25680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (25680)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (25680)Memory used [KB]: 6396
% 0.20/0.57  % (25680)Time elapsed: 0.167 s
% 0.20/0.57  % (25680)------------------------------
% 0.20/0.57  % (25680)------------------------------
% 0.20/0.57  % (25675)Success in time 0.215 s
%------------------------------------------------------------------------------
