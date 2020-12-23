%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:05 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 261 expanded)
%              Number of leaves         :    9 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  180 ( 794 expanded)
%              Number of equality atoms :   25 (  78 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(subsumption_resolution,[],[f219,f46])).

fof(f46,plain,(
    ~ v2_tex_2(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f27,f43])).

fof(f43,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f37,f25])).

fof(f25,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f27,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f219,plain,(
    v2_tex_2(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f218,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f218,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f217,f87])).

fof(f87,plain,(
    k1_xboole_0 = sK2(sK0,k1_xboole_0) ),
    inference(resolution,[],[f74,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f74,plain,(
    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f73,f46])).

fof(f73,plain,
    ( r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK0) ),
    inference(resolution,[],[f54,f29])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f36,f30])).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

% (22872)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(f217,plain,
    ( k1_xboole_0 != sK2(sK0,k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | v2_tex_2(k1_xboole_0,sK0) ),
    inference(resolution,[],[f165,f59])).

fof(f59,plain,(
    v3_pre_topc(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f58,f28])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_xboole_0,sK0) ),
    inference(resolution,[],[f53,f29])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f52,f44])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f25,f43])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(k1_xboole_0)
      | v3_pre_topc(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f40,f30])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f165,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k1_xboole_0,X1)
      | k1_xboole_0 != sK2(X1,k1_xboole_0)
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f164,f115])).

fof(f115,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f94,f37])).

fof(f94,plain,(
    ! [X0] : v1_xboole_0(k3_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f64,f44])).

fof(f64,plain,(
    ! [X6,X7] :
      ( ~ v1_xboole_0(X6)
      | v1_xboole_0(k3_xboole_0(X7,k1_xboole_0)) ) ),
    inference(resolution,[],[f51,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f51,plain,(
    ! [X0,X1] : m1_subset_1(k3_xboole_0(X1,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f49,f50])).

fof(f50,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f42,f30])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f49,plain,(
    ! [X0,X1] : m1_subset_1(k9_subset_1(X0,X1,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f41,f30])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f164,plain,(
    ! [X1] :
      ( sK2(X1,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ v3_pre_topc(k1_xboole_0,X1)
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f129,f115])).

fof(f129,plain,(
    ! [X2,X1] :
      ( ~ v3_pre_topc(k1_xboole_0,X1)
      | sK2(X1,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0))
      | ~ l1_pre_topc(X1)
      | v2_tex_2(k1_xboole_0,X1) ) ),
    inference(backward_demodulation,[],[f84,f115])).

fof(f84,plain,(
    ! [X2,X1] :
      ( sK2(X1,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0))
      | ~ l1_pre_topc(X1)
      | ~ v3_pre_topc(k3_xboole_0(X2,k1_xboole_0),X1)
      | v2_tex_2(k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f82,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k9_subset_1(X0,X1,k3_xboole_0(X2,k1_xboole_0)) = k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0)) ),
    inference(resolution,[],[f51,f42])).

fof(f82,plain,(
    ! [X2,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v3_pre_topc(k3_xboole_0(X2,k1_xboole_0),X1)
      | sK2(X1,k1_xboole_0) != k9_subset_1(u1_struct_0(X1),k1_xboole_0,k3_xboole_0(X2,k1_xboole_0))
      | v2_tex_2(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f60,f51])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | sK2(X0,k1_xboole_0) != k9_subset_1(u1_struct_0(X0),k1_xboole_0,X1)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f31,f30])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:31:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.45  % (22866)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.46  % (22860)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.46  % (22862)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.46  % (22858)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.46  % (22858)Refutation not found, incomplete strategy% (22858)------------------------------
% 0.19/0.46  % (22858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (22858)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (22858)Memory used [KB]: 6140
% 0.19/0.46  % (22858)Time elapsed: 0.061 s
% 0.19/0.46  % (22858)------------------------------
% 0.19/0.46  % (22858)------------------------------
% 0.19/0.47  % (22864)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.47  % (22871)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.47  % (22875)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.47  % (22870)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.47  % (22875)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f220,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(subsumption_resolution,[],[f219,f46])).
% 0.19/0.47  fof(f46,plain,(
% 0.19/0.47    ~v2_tex_2(k1_xboole_0,sK0)),
% 0.19/0.47    inference(backward_demodulation,[],[f27,f43])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    k1_xboole_0 = sK1),
% 0.19/0.47    inference(resolution,[],[f37,f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    v1_xboole_0(sK1)),
% 0.19/0.47    inference(cnf_transformation,[],[f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.47    inference(flattening,[],[f14])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,plain,(
% 0.19/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.19/0.47    inference(pure_predicate_removal,[],[f11])).
% 0.19/0.47  fof(f11,negated_conjecture,(
% 0.19/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.19/0.47    inference(negated_conjecture,[],[f10])).
% 0.19/0.47  fof(f10,conjecture,(
% 0.19/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ~v2_tex_2(sK1,sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f15])).
% 0.19/0.47  fof(f219,plain,(
% 0.19/0.47    v2_tex_2(k1_xboole_0,sK0)),
% 0.19/0.47    inference(subsumption_resolution,[],[f218,f29])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    l1_pre_topc(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f15])).
% 0.19/0.47  fof(f218,plain,(
% 0.19/0.47    ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0)),
% 0.19/0.47    inference(subsumption_resolution,[],[f217,f87])).
% 0.19/0.47  fof(f87,plain,(
% 0.19/0.47    k1_xboole_0 = sK2(sK0,k1_xboole_0)),
% 0.19/0.47    inference(resolution,[],[f74,f39])).
% 0.19/0.47  fof(f39,plain,(
% 0.19/0.47    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.19/0.47    inference(ennf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.19/0.47  fof(f74,plain,(
% 0.19/0.47    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)),
% 0.19/0.47    inference(subsumption_resolution,[],[f73,f46])).
% 0.19/0.47  fof(f73,plain,(
% 0.19/0.47    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) | v2_tex_2(k1_xboole_0,sK0)),
% 0.19/0.47    inference(resolution,[],[f54,f29])).
% 0.19/0.47  fof(f54,plain,(
% 0.19/0.47    ( ! [X0] : (~l1_pre_topc(X0) | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.19/0.47    inference(resolution,[],[f36,f30])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.19/0.47  fof(f36,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f17])).
% 0.19/0.47  % (22872)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.47    inference(flattening,[],[f16])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,axiom,(
% 0.19/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
% 0.19/0.47  fof(f217,plain,(
% 0.19/0.47    k1_xboole_0 != sK2(sK0,k1_xboole_0) | ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0)),
% 0.19/0.47    inference(resolution,[],[f165,f59])).
% 0.19/0.47  fof(f59,plain,(
% 0.19/0.47    v3_pre_topc(k1_xboole_0,sK0)),
% 0.19/0.47    inference(subsumption_resolution,[],[f58,f28])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    v2_pre_topc(sK0)),
% 0.19/0.47    inference(cnf_transformation,[],[f15])).
% 0.19/0.47  fof(f58,plain,(
% 0.19/0.47    ~v2_pre_topc(sK0) | v3_pre_topc(k1_xboole_0,sK0)),
% 0.19/0.47    inference(resolution,[],[f53,f29])).
% 0.19/0.47  fof(f53,plain,(
% 0.19/0.47    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_xboole_0,X0)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f52,f44])).
% 0.19/0.47  fof(f44,plain,(
% 0.19/0.47    v1_xboole_0(k1_xboole_0)),
% 0.19/0.47    inference(backward_demodulation,[],[f25,f43])).
% 0.19/0.47  fof(f52,plain,(
% 0.19/0.47    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(k1_xboole_0) | v3_pre_topc(k1_xboole_0,X0)) )),
% 0.19/0.47    inference(resolution,[],[f40,f30])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(X1) | v3_pre_topc(X1,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.47    inference(flattening,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,axiom,(
% 0.19/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).
% 0.19/0.47  fof(f165,plain,(
% 0.19/0.47    ( ! [X1] : (~v3_pre_topc(k1_xboole_0,X1) | k1_xboole_0 != sK2(X1,k1_xboole_0) | ~l1_pre_topc(X1) | v2_tex_2(k1_xboole_0,X1)) )),
% 0.19/0.47    inference(forward_demodulation,[],[f164,f115])).
% 0.19/0.47  fof(f115,plain,(
% 0.19/0.47    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.19/0.47    inference(resolution,[],[f94,f37])).
% 0.19/0.47  fof(f94,plain,(
% 0.19/0.47    ( ! [X0] : (v1_xboole_0(k3_xboole_0(X0,k1_xboole_0))) )),
% 0.19/0.47    inference(resolution,[],[f64,f44])).
% 0.19/0.47  fof(f64,plain,(
% 0.19/0.47    ( ! [X6,X7] : (~v1_xboole_0(X6) | v1_xboole_0(k3_xboole_0(X7,k1_xboole_0))) )),
% 0.19/0.47    inference(resolution,[],[f51,f38])).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.19/0.47  fof(f51,plain,(
% 0.19/0.47    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X1,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.19/0.47    inference(backward_demodulation,[],[f49,f50])).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.19/0.47    inference(resolution,[],[f42,f30])).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.19/0.47  fof(f49,plain,(
% 0.19/0.47    ( ! [X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.19/0.47    inference(resolution,[],[f41,f30])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.19/0.47    inference(ennf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.19/0.47  fof(f164,plain,(
% 0.19/0.47    ( ! [X1] : (sK2(X1,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~v3_pre_topc(k1_xboole_0,X1) | ~l1_pre_topc(X1) | v2_tex_2(k1_xboole_0,X1)) )),
% 0.19/0.47    inference(forward_demodulation,[],[f129,f115])).
% 0.19/0.47  fof(f129,plain,(
% 0.19/0.47    ( ! [X2,X1] : (~v3_pre_topc(k1_xboole_0,X1) | sK2(X1,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0)) | ~l1_pre_topc(X1) | v2_tex_2(k1_xboole_0,X1)) )),
% 0.19/0.47    inference(backward_demodulation,[],[f84,f115])).
% 0.19/0.47  fof(f84,plain,(
% 0.19/0.47    ( ! [X2,X1] : (sK2(X1,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k3_xboole_0(X2,k1_xboole_0)) | ~l1_pre_topc(X1) | ~v3_pre_topc(k3_xboole_0(X2,k1_xboole_0),X1) | v2_tex_2(k1_xboole_0,X1)) )),
% 0.19/0.47    inference(forward_demodulation,[],[f82,f62])).
% 0.19/0.47  fof(f62,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_xboole_0(X2,k1_xboole_0)) = k3_xboole_0(X1,k3_xboole_0(X2,k1_xboole_0))) )),
% 0.19/0.47    inference(resolution,[],[f51,f42])).
% 0.19/0.47  fof(f82,plain,(
% 0.19/0.47    ( ! [X2,X1] : (~l1_pre_topc(X1) | ~v3_pre_topc(k3_xboole_0(X2,k1_xboole_0),X1) | sK2(X1,k1_xboole_0) != k9_subset_1(u1_struct_0(X1),k1_xboole_0,k3_xboole_0(X2,k1_xboole_0)) | v2_tex_2(k1_xboole_0,X1)) )),
% 0.19/0.47    inference(resolution,[],[f60,f51])).
% 0.19/0.47  fof(f60,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | sK2(X0,k1_xboole_0) != k9_subset_1(u1_struct_0(X0),k1_xboole_0,X1) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.19/0.47    inference(resolution,[],[f31,f30])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ( ! [X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f17])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (22875)------------------------------
% 0.19/0.47  % (22875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (22875)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (22875)Memory used [KB]: 1791
% 0.19/0.47  % (22875)Time elapsed: 0.078 s
% 0.19/0.47  % (22859)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.47  % (22875)------------------------------
% 0.19/0.47  % (22875)------------------------------
% 0.19/0.48  % (22854)Success in time 0.13 s
%------------------------------------------------------------------------------
