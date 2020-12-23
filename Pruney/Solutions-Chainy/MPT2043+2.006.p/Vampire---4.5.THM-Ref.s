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
% DateTime   : Thu Dec  3 13:23:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 111 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :   15
%              Number of atoms          :  167 ( 371 expanded)
%              Number of equality atoms :   24 (  56 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f334,plain,(
    $false ),
    inference(resolution,[],[f281,f61])).

fof(f61,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f28,f29])).

fof(f29,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f28,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f281,plain,(
    v1_subset_1(sK1,sK1) ),
    inference(backward_demodulation,[],[f62,f278])).

fof(f278,plain,(
    sK1 = k9_setfam_1(sK0) ),
    inference(global_subsumption,[],[f63,f276])).

fof(f276,plain,
    ( sK1 = k9_setfam_1(sK0)
    | ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) ),
    inference(duplicate_literal_removal,[],[f273])).

fof(f273,plain,
    ( sK1 = k9_setfam_1(sK0)
    | ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))
    | ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))
    | sK1 = k9_setfam_1(sK0) ),
    inference(resolution,[],[f271,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f37,f30])).

fof(f30,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK4(X0,X1),X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

fof(f271,plain,(
    ! [X3] :
      ( r2_hidden(sK4(k9_setfam_1(sK0),X3),sK1)
      | k9_setfam_1(sK0) = X3
      | ~ m1_subset_1(X3,k9_setfam_1(k9_setfam_1(sK0))) ) ),
    inference(global_subsumption,[],[f20,f268])).

fof(f268,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k9_setfam_1(k9_setfam_1(sK0)))
      | k9_setfam_1(sK0) = X3
      | ~ r2_hidden(sK2,sK1)
      | r2_hidden(sK4(k9_setfam_1(sK0),X3),sK1) ) ),
    inference(resolution,[],[f253,f85])).

fof(f85,plain,(
    ! [X0] : r1_tarski(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f69,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f69,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f21,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f21,plain,(
    v1_xboole_0(sK2) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

fof(f253,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X6,sK4(k9_setfam_1(sK0),X5))
      | ~ m1_subset_1(X5,k9_setfam_1(k9_setfam_1(sK0)))
      | k9_setfam_1(sK0) = X5
      | ~ r2_hidden(X6,sK1)
      | r2_hidden(sK4(k9_setfam_1(sK0),X5),sK1) ) ),
    inference(resolution,[],[f124,f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK0)
      | ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(X1,sK1) ) ),
    inference(global_subsumption,[],[f63,f198])).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,sK0)
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(X1,sK1)
      | ~ m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) ) ),
    inference(resolution,[],[f68,f49])).

fof(f49,plain,(
    v13_waybel_0(sK1,k2_yellow_1(k9_setfam_1(sK0))) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f31,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f25,plain,(
    v13_waybel_0(sK1,k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X3,X0)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0))) ) ),
    inference(forward_demodulation,[],[f58,f32])).

fof(f32,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X0)))))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X3,X0)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0))) ) ),
    inference(definition_unfolding,[],[f38,f30,f31,f31])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X3,X0)
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).

fof(f124,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK4(k9_setfam_1(X1),X0),X1)
      | k9_setfam_1(X1) = X0
      | ~ m1_subset_1(X0,k9_setfam_1(k9_setfam_1(X1))) ) ),
    inference(resolution,[],[f53,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),X0)
      | ~ m1_subset_1(X1,k9_setfam_1(X0))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,(
    m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) ),
    inference(backward_demodulation,[],[f48,f32])).

fof(f48,plain,(
    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))))) ),
    inference(definition_unfolding,[],[f26,f30,f31])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    v1_subset_1(sK1,k9_setfam_1(sK0)) ),
    inference(backward_demodulation,[],[f51,f32])).

fof(f51,plain,(
    v1_subset_1(sK1,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))) ),
    inference(definition_unfolding,[],[f23,f31])).

fof(f23,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:29:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.53  % (11675)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.53  % (11689)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (11666)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (11667)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (11670)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (11681)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (11667)Refutation not found, incomplete strategy% (11667)------------------------------
% 0.22/0.54  % (11667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11667)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11667)Memory used [KB]: 10746
% 0.22/0.54  % (11667)Time elapsed: 0.113 s
% 0.22/0.54  % (11667)------------------------------
% 0.22/0.54  % (11667)------------------------------
% 0.22/0.54  % (11671)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (11668)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (11675)Refutation not found, incomplete strategy% (11675)------------------------------
% 0.22/0.54  % (11675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11689)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 1.40/0.54  % (11669)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  fof(f334,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(resolution,[],[f281,f61])).
% 1.40/0.54  fof(f61,plain,(
% 1.40/0.54    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 1.40/0.54    inference(backward_demodulation,[],[f28,f29])).
% 1.40/0.54  fof(f29,plain,(
% 1.40/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.40/0.54    inference(cnf_transformation,[],[f3])).
% 1.40/0.54  fof(f3,axiom,(
% 1.40/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.40/0.54  fof(f28,plain,(
% 1.40/0.54    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f5])).
% 1.40/0.54  fof(f5,axiom,(
% 1.40/0.54    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).
% 1.40/0.54  fof(f281,plain,(
% 1.40/0.54    v1_subset_1(sK1,sK1)),
% 1.40/0.54    inference(backward_demodulation,[],[f62,f278])).
% 1.40/0.54  fof(f278,plain,(
% 1.40/0.54    sK1 = k9_setfam_1(sK0)),
% 1.40/0.54    inference(global_subsumption,[],[f63,f276])).
% 1.40/0.54  fof(f276,plain,(
% 1.40/0.54    sK1 = k9_setfam_1(sK0) | ~m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))),
% 1.40/0.54    inference(duplicate_literal_removal,[],[f273])).
% 1.40/0.54  fof(f273,plain,(
% 1.40/0.54    sK1 = k9_setfam_1(sK0) | ~m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) | ~m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0))) | sK1 = k9_setfam_1(sK0)),
% 1.40/0.54    inference(resolution,[],[f271,f52])).
% 1.40/0.54  fof(f52,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~m1_subset_1(X1,k9_setfam_1(X0)) | X0 = X1) )),
% 1.40/0.54    inference(definition_unfolding,[],[f37,f30])).
% 1.40/0.54  fof(f30,plain,(
% 1.40/0.54    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f7])).
% 1.40/0.54  fof(f7,axiom,(
% 1.40/0.54    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 1.40/0.54  fof(f37,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK4(X0,X1),X1) | X0 = X1) )),
% 1.40/0.54    inference(cnf_transformation,[],[f16])).
% 1.40/0.54  fof(f16,plain,(
% 1.40/0.54    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.54    inference(flattening,[],[f15])).
% 1.40/0.54  fof(f15,plain,(
% 1.40/0.54    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f4])).
% 1.40/0.54  fof(f4,axiom,(
% 1.40/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).
% 1.40/0.54  fof(f271,plain,(
% 1.40/0.54    ( ! [X3] : (r2_hidden(sK4(k9_setfam_1(sK0),X3),sK1) | k9_setfam_1(sK0) = X3 | ~m1_subset_1(X3,k9_setfam_1(k9_setfam_1(sK0)))) )),
% 1.40/0.54    inference(global_subsumption,[],[f20,f268])).
% 1.40/0.54  fof(f268,plain,(
% 1.40/0.54    ( ! [X3] : (~m1_subset_1(X3,k9_setfam_1(k9_setfam_1(sK0))) | k9_setfam_1(sK0) = X3 | ~r2_hidden(sK2,sK1) | r2_hidden(sK4(k9_setfam_1(sK0),X3),sK1)) )),
% 1.40/0.54    inference(resolution,[],[f253,f85])).
% 1.40/0.54  fof(f85,plain,(
% 1.40/0.54    ( ! [X0] : (r1_tarski(sK2,X0)) )),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f69,f44])).
% 1.40/0.54  fof(f44,plain,(
% 1.40/0.54    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f19])).
% 1.40/0.54  fof(f19,plain,(
% 1.40/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f2])).
% 1.40/0.54  fof(f2,axiom,(
% 1.40/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.40/0.54  fof(f69,plain,(
% 1.40/0.54    ( ! [X0] : (~r2_hidden(X0,sK2)) )),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f21,f35])).
% 1.40/0.54  fof(f35,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f1])).
% 1.40/0.54  fof(f1,axiom,(
% 1.40/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.40/0.54  fof(f21,plain,(
% 1.40/0.54    v1_xboole_0(sK2)),
% 1.40/0.54    inference(cnf_transformation,[],[f14])).
% 1.40/0.54  fof(f14,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.40/0.54    inference(flattening,[],[f13])).
% 1.40/0.54  fof(f13,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : (? [X2] : (v1_xboole_0(X2) & r2_hidden(X2,X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f12])).
% 1.40/0.54  fof(f12,negated_conjecture,(
% 1.40/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 1.40/0.54    inference(negated_conjecture,[],[f11])).
% 1.40/0.54  fof(f11,conjecture,(
% 1.40/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) & v13_waybel_0(X1,k3_yellow_1(X0)) & v2_waybel_0(X1,k3_yellow_1(X0)) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(X0))) & ~v1_xboole_0(X1)) => ! [X2] : ~(v1_xboole_0(X2) & r2_hidden(X2,X1))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).
% 1.40/0.54  fof(f253,plain,(
% 1.40/0.54    ( ! [X6,X5] : (~r1_tarski(X6,sK4(k9_setfam_1(sK0),X5)) | ~m1_subset_1(X5,k9_setfam_1(k9_setfam_1(sK0))) | k9_setfam_1(sK0) = X5 | ~r2_hidden(X6,sK1) | r2_hidden(sK4(k9_setfam_1(sK0),X5),sK1)) )),
% 1.40/0.54    inference(resolution,[],[f124,f201])).
% 1.40/0.54  fof(f201,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r1_tarski(X1,sK0) | ~r1_tarski(X0,X1) | ~r2_hidden(X0,sK1) | r2_hidden(X1,sK1)) )),
% 1.40/0.54    inference(global_subsumption,[],[f63,f198])).
% 1.40/0.54  fof(f198,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,sK0) | ~r2_hidden(X0,sK1) | r2_hidden(X1,sK1) | ~m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))) )),
% 1.40/0.54    inference(resolution,[],[f68,f49])).
% 1.40/0.54  fof(f49,plain,(
% 1.40/0.54    v13_waybel_0(sK1,k2_yellow_1(k9_setfam_1(sK0)))),
% 1.40/0.54    inference(definition_unfolding,[],[f25,f31])).
% 1.40/0.54  fof(f31,plain,(
% 1.40/0.54    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f9])).
% 1.40/0.54  fof(f9,axiom,(
% 1.40/0.54    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 1.40/0.54  fof(f25,plain,(
% 1.40/0.54    v13_waybel_0(sK1,k3_yellow_1(sK0))),
% 1.40/0.54    inference(cnf_transformation,[],[f14])).
% 1.40/0.54  fof(f68,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0))) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,X0) | ~r2_hidden(X2,X1) | r2_hidden(X3,X1) | ~m1_subset_1(X1,k9_setfam_1(k9_setfam_1(X0)))) )),
% 1.40/0.54    inference(forward_demodulation,[],[f58,f32])).
% 1.40/0.54  fof(f32,plain,(
% 1.40/0.54    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 1.40/0.54    inference(cnf_transformation,[],[f8])).
% 1.40/0.54  fof(f8,axiom,(
% 1.40/0.54    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 1.40/0.54  fof(f58,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(X0))))) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,X0) | ~r2_hidden(X2,X1) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,k2_yellow_1(k9_setfam_1(X0)))) )),
% 1.40/0.54    inference(definition_unfolding,[],[f38,f30,f31,f31])).
% 1.40/0.55  fof(f38,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) | ~r1_tarski(X2,X3) | ~r1_tarski(X3,X0) | ~r2_hidden(X2,X1) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,k3_yellow_1(X0))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f18])).
% 1.40/0.55  fof(f18,plain,(
% 1.40/0.55    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 1.40/0.55    inference(flattening,[],[f17])).
% 1.40/0.55  fof(f17,plain,(
% 1.40/0.55    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | (~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 1.40/0.55    inference(ennf_transformation,[],[f10])).
% 1.40/0.55  fof(f10,axiom,(
% 1.40/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) => (v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : ((r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => r2_hidden(X3,X1))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).
% 1.40/0.55  fof(f124,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r1_tarski(sK4(k9_setfam_1(X1),X0),X1) | k9_setfam_1(X1) = X0 | ~m1_subset_1(X0,k9_setfam_1(k9_setfam_1(X1)))) )),
% 1.40/0.55    inference(resolution,[],[f53,f59])).
% 1.40/0.55  fof(f59,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k9_setfam_1(X1)) | r1_tarski(X0,X1)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f47,f30])).
% 1.40/0.55  fof(f47,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f6])).
% 1.40/0.55  fof(f6,axiom,(
% 1.40/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.40/0.55  fof(f53,plain,(
% 1.40/0.55    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),X0) | ~m1_subset_1(X1,k9_setfam_1(X0)) | X0 = X1) )),
% 1.40/0.55    inference(definition_unfolding,[],[f36,f30])).
% 1.40/0.55  fof(f36,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK4(X0,X1),X0) | X0 = X1) )),
% 1.40/0.55    inference(cnf_transformation,[],[f16])).
% 1.40/0.55  fof(f20,plain,(
% 1.40/0.55    r2_hidden(sK2,sK1)),
% 1.40/0.55    inference(cnf_transformation,[],[f14])).
% 1.40/0.55  fof(f63,plain,(
% 1.40/0.55    m1_subset_1(sK1,k9_setfam_1(k9_setfam_1(sK0)))),
% 1.40/0.55    inference(backward_demodulation,[],[f48,f32])).
% 1.40/0.55  fof(f48,plain,(
% 1.40/0.55    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(k2_yellow_1(k9_setfam_1(sK0)))))),
% 1.40/0.55    inference(definition_unfolding,[],[f26,f30,f31])).
% 1.40/0.55  fof(f26,plain,(
% 1.40/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(sK0))))),
% 1.40/0.55    inference(cnf_transformation,[],[f14])).
% 1.40/0.55  fof(f62,plain,(
% 1.40/0.55    v1_subset_1(sK1,k9_setfam_1(sK0))),
% 1.40/0.55    inference(backward_demodulation,[],[f51,f32])).
% 1.40/0.55  fof(f51,plain,(
% 1.40/0.55    v1_subset_1(sK1,u1_struct_0(k2_yellow_1(k9_setfam_1(sK0))))),
% 1.40/0.55    inference(definition_unfolding,[],[f23,f31])).
% 1.40/0.55  fof(f23,plain,(
% 1.40/0.55    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(sK0)))),
% 1.40/0.55    inference(cnf_transformation,[],[f14])).
% 1.40/0.55  % SZS output end Proof for theBenchmark
% 1.40/0.55  % (11689)------------------------------
% 1.40/0.55  % (11689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (11689)Termination reason: Refutation
% 1.40/0.55  
% 1.40/0.55  % (11689)Memory used [KB]: 6396
% 1.40/0.55  % (11689)Time elapsed: 0.123 s
% 1.40/0.55  % (11689)------------------------------
% 1.40/0.55  % (11689)------------------------------
% 1.40/0.55  % (11691)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.55  % (11664)Success in time 0.177 s
%------------------------------------------------------------------------------
