%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 138 expanded)
%              Number of leaves         :   14 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  186 ( 445 expanded)
%              Number of equality atoms :   17 (  50 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f466,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f153,f165,f381,f432,f465])).

fof(f465,plain,(
    ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f433,f434,f67])).

fof(f67,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X1)))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0)))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f50,plain,(
    ! [X0] : k1_zfmisc_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(definition_unfolding,[],[f49,f43])).

fof(f43,plain,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f434,plain,
    ( m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK1)))
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f51,f376])).

fof(f376,plain,
    ( sK1 = u1_struct_0(k3_yellow_1(sK0))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl8_5
  <=> sK1 = u1_struct_0(k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f51,plain,(
    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0))))) ),
    inference(definition_unfolding,[],[f25,f50])).

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

fof(f433,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f22,f376])).

fof(f22,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f432,plain,
    ( ~ spl8_2
    | spl8_6 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | ~ spl8_2
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f401,f383,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,u1_struct_0(k3_yellow_1(X0)))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | u1_struct_0(k3_yellow_1(X0)) != X1 ) ),
    inference(definition_unfolding,[],[f28,f50])).

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

fof(f383,plain,
    ( r2_hidden(sK4(u1_struct_0(k3_yellow_1(sK0)),sK1),u1_struct_0(k3_yellow_1(sK0)))
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f380,f32])).

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

fof(f380,plain,
    ( ~ r1_tarski(u1_struct_0(k3_yellow_1(sK0)),sK1)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl8_6
  <=> r1_tarski(u1_struct_0(k3_yellow_1(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f401,plain,
    ( ~ r1_tarski(sK4(u1_struct_0(k3_yellow_1(sK0)),sK1),sK0)
    | ~ spl8_2
    | spl8_6 ),
    inference(unit_resulting_resolution,[],[f380,f19,f80,f201])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK4(X1,sK1),sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ r1_tarski(X0,sK4(X1,sK1))
        | r1_tarski(X1,sK1) )
    | ~ spl8_2 ),
    inference(resolution,[],[f152,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,sK1)
        | ~ r1_tarski(X0,X1)
        | ~ r2_hidden(X0,sK1)
        | ~ r1_tarski(X1,sK0) )
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl8_2
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | r2_hidden(X1,sK1)
        | ~ r2_hidden(X0,sK1)
        | ~ r1_tarski(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f80,plain,(
    ! [X0] : r1_tarski(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f70,f32])).

fof(f70,plain,(
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

fof(f19,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f381,plain,
    ( spl8_5
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f132,f378,f374])).

fof(f132,plain,
    ( ~ r1_tarski(u1_struct_0(k3_yellow_1(sK0)),sK1)
    | sK1 = u1_struct_0(k3_yellow_1(sK0)) ),
    inference(resolution,[],[f117,f48])).

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

fof(f117,plain,(
    r1_tarski(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f51,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1)))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f50])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f165,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f24,f149])).

fof(f149,plain,
    ( ~ v13_waybel_0(sK1,k3_yellow_1(sK0))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl8_1
  <=> v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f24,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f153,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f118,f151,f147])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,sK0)
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(X1,sK1)
      | ~ v13_waybel_0(sK1,k3_yellow_1(sK0)) ) ),
    inference(resolution,[],[f51,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0)))))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X3,X0)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(definition_unfolding,[],[f36,f50])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_7)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:25:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.47  % (4491)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.48  % (4482)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.49  % (4474)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (4469)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (4471)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (4472)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (4477)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (4484)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (4493)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (4468)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (4480)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (4490)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (4476)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (4471)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f466,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f153,f165,f381,f432,f465])).
% 0.20/0.52  fof(f465,plain,(
% 0.20/0.52    ~spl8_5),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f461])).
% 0.20/0.52  fof(f461,plain,(
% 0.20/0.52    $false | ~spl8_5),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f433,f434,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X1))) | ~v1_subset_1(X1,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f42,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0] : (k1_zfmisc_1(X0) = u1_struct_0(k3_yellow_1(X0))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f49,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0] : (k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : k9_setfam_1(X0) = u1_struct_0(k3_yellow_1(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_waybel_7)).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.52  fof(f434,plain,(
% 0.20/0.52    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK1))) | ~spl8_5),
% 0.20/0.52    inference(backward_demodulation,[],[f51,f376])).
% 0.20/0.52  fof(f376,plain,(
% 0.20/0.52    sK1 = u1_struct_0(k3_yellow_1(sK0)) | ~spl8_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f374])).
% 0.20/0.52  fof(f374,plain,(
% 0.20/0.52    spl8_5 <=> sK1 = u1_struct_0(k3_yellow_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    m1_subset_1(sK1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(sK0)))))),
% 0.20/0.52    inference(definition_unfolding,[],[f25,f50])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.20/0.52    inference(negated_conjecture,[],[f11])).
% 0.20/0.52  fof(f11,conjecture,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow19)).
% 0.20/0.52  fof(f433,plain,(
% 0.20/0.52    v1_subset_1(sK1,sK1) | ~spl8_5),
% 0.20/0.52    inference(backward_demodulation,[],[f22,f376])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f432,plain,(
% 0.20/0.52    ~spl8_2 | spl8_6),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f425])).
% 0.20/0.52  fof(f425,plain,(
% 0.20/0.52    $false | (~spl8_2 | spl8_6)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f401,f383,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X2,X0] : (~r2_hidden(X2,u1_struct_0(k3_yellow_1(X0))) | r1_tarski(X2,X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | u1_struct_0(k3_yellow_1(X0)) != X1) )),
% 0.20/0.52    inference(definition_unfolding,[],[f28,f50])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.52  fof(f383,plain,(
% 0.20/0.52    r2_hidden(sK4(u1_struct_0(k3_yellow_1(sK0)),sK1),u1_struct_0(k3_yellow_1(sK0))) | spl8_6),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f380,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f380,plain,(
% 0.20/0.52    ~r1_tarski(u1_struct_0(k3_yellow_1(sK0)),sK1) | spl8_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f378])).
% 0.20/0.52  fof(f378,plain,(
% 0.20/0.52    spl8_6 <=> r1_tarski(u1_struct_0(k3_yellow_1(sK0)),sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.52  fof(f401,plain,(
% 0.20/0.52    ~r1_tarski(sK4(u1_struct_0(k3_yellow_1(sK0)),sK1),sK0) | (~spl8_2 | spl8_6)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f380,f19,f80,f201])).
% 0.20/0.52  fof(f201,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(sK4(X1,sK1),sK0) | ~r2_hidden(X0,sK1) | ~r1_tarski(X0,sK4(X1,sK1)) | r1_tarski(X1,sK1)) ) | ~spl8_2),
% 0.20/0.52    inference(resolution,[],[f152,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X1,sK1) | ~r1_tarski(X0,X1) | ~r2_hidden(X0,sK1) | ~r1_tarski(X1,sK0)) ) | ~spl8_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f151])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    spl8_2 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | r2_hidden(X1,sK1) | ~r2_hidden(X0,sK1) | ~r1_tarski(X1,sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(sK2,X0)) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f70,f32])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK2)) )),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f20,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    v1_xboole_0(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    r2_hidden(sK2,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f381,plain,(
% 0.20/0.52    spl8_5 | ~spl8_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f132,f378,f374])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    ~r1_tarski(u1_struct_0(k3_yellow_1(sK0)),sK1) | sK1 = u1_struct_0(k3_yellow_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f117,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    r1_tarski(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f51,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k3_yellow_1(X1))) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f35,f50])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f165,plain,(
% 0.20/0.52    spl8_1),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f154])).
% 0.20/0.52  fof(f154,plain,(
% 0.20/0.52    $false | spl8_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f24,f149])).
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    ~v13_waybel_0(sK1,k3_yellow_1(sK0)) | spl8_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f147])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    spl8_1 <=> v13_waybel_0(sK1,k3_yellow_1(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    v13_waybel_0(sK1,k3_yellow_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    ~spl8_1 | spl8_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f118,f151,f147])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,sK0) | ~r2_hidden(X0,sK1) | r2_hidden(X1,sK1) | ~v13_waybel_0(sK1,k3_yellow_1(sK0))) )),
% 0.20/0.52    inference(resolution,[],[f51,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,u1_struct_0(k3_yellow_1(u1_struct_0(k3_yellow_1(X0))))) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,X0) | ~r2_hidden(X2,X1) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,k3_yellow_1(X0))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f36,f50])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,X0) | ~r2_hidden(X2,X1) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,k3_yellow_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | (~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) => (v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : ((r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => r2_hidden(X3,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_waybel_7)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (4471)------------------------------
% 0.20/0.52  % (4471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4471)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (4471)Memory used [KB]: 6396
% 0.20/0.52  % (4471)Time elapsed: 0.124 s
% 0.20/0.52  % (4471)------------------------------
% 0.20/0.52  % (4471)------------------------------
% 0.20/0.52  % (4465)Success in time 0.174 s
%------------------------------------------------------------------------------
